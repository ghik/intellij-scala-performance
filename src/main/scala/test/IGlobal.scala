package test

import scala.tools.nsc.interactive.Global
import scala.collection.mutable.LinkedHashMap
import scala.tools.nsc.{symtab, Settings}
import scala.tools.nsc.reporters.Reporter

class IGlobal(settings: Settings, reporter: Reporter) extends Global(settings, reporter) {

  import definitions._
  import analyzer.{SearchResult, ImplicitSearch}
  import symtab.Flags._

  private val Dollar = newTermName("$")

  private class Members[M <: Member] extends LinkedHashMap[Name, Set[M]] {
    override def default(key: Name) = Set()

    private def matching(sym: Symbol, symtpe: Type, ms: Set[M]): Option[M] = ms.find { m =>
      (m.sym.name == sym.name) && (m.sym.isType || (m.tpe matches symtpe))
    }

    private def keepSecond(m: M, sym: Symbol, implicitlyAdded: Boolean): Boolean =
      m.sym.hasFlag(ACCESSOR | PARAMACCESSOR) &&
        !sym.hasFlag(ACCESSOR | PARAMACCESSOR) &&
        (!implicitlyAdded || m.implicitlyAdded)

    def add(sym: Symbol, pre: Type, implicitlyAdded: Boolean)(toMember: (Symbol, Type) => M) {
      if ((sym.isGetter || sym.isSetter) && sym.accessed != NoSymbol) {
        add(sym.accessed, pre, implicitlyAdded)(toMember)
      } else if (!sym.name.decodedName.containsName(Dollar) && !sym.isSynthetic && sym.hasRawInfo) {
        val symtpe = pre.memberType(sym) onTypeError ErrorType
        matching(sym, symtpe, this(sym.name)) match {
          case Some(m) =>
            if (keepSecond(m, sym, implicitlyAdded)) {
              //print(" -+ "+sym.name)
              this(sym.name) = this(sym.name) - m + toMember(sym, symtpe)
            }
          case None =>
            //print(" + "+sym.name)
            this(sym.name) = this(sym.name) + toMember(sym, symtpe)
        }
      }
    }

    def addNonShadowed(other: Members[M]) = {
      for ((name, ms) <- other)
        if (ms.nonEmpty && this(name).isEmpty) this(name) = ms
    }

    def allMembers: List[M] = values.toList.flatten
  }

  private def typeMembers(pos: Position): Stream[List[TypeMember]] = {
    var tree: Tree = EmptyTree

    // if tree consists of just x. or x.fo where fo is not yet a full member name
    // ignore the selection and look in just x.
    tree match {
      case Select(qual, name) if tree.tpe == ErrorType => tree = qual
      case _ =>
    }

    val context = doLocateContext(pos)

    val shouldTypeQualifier = tree.tpe match {
      case null           => true
      case mt: MethodType => mt.isImplicit
      case _              => false
    }

    if (shouldTypeQualifier)
    // TODO: guard with try/catch to deal with ill-typed qualifiers.
      tree = analyzer.newTyper(context).typedQualifier(tree)

    debugLog("typeMembers at "+tree+" "+tree.tpe)

    val superAccess = tree.isInstanceOf[Super]
    val members = new Members[TypeMember]

    def addTypeMember(sym: Symbol, pre: Type, inherited: Boolean, viaView: Symbol) = {
      val implicitlyAdded = viaView != NoSymbol
      members.add(sym, pre, implicitlyAdded) { (s, st) =>
        new TypeMember(s, st,
          context.isAccessible(if (s.hasGetter) s.getter(s.owner) else s, pre, superAccess && !implicitlyAdded),
          inherited,
          viaView)
      }
    }

    /** Create a function application of a given view function to `tree` and typechecked it.
      */
    def viewApply(view: SearchResult): Tree = {
      assert(view.tree != EmptyTree)
      analyzer.newTyper(context.makeImplicit(reportAmbiguousErrors = false))
        .typed(Apply(view.tree, List(tree)) setPos tree.pos)
        .onTypeError(EmptyTree)
    }

    val pre = stabilizedType(tree)

    val ownerTpe = tree.tpe match {
      case analyzer.ImportType(expr) => expr.tpe
      case null => pre
      case MethodType(List(), rtpe) => rtpe
      case _ => tree.tpe
    }

    //print("add members")
    for (sym <- ownerTpe.members)
      addTypeMember(sym, pre, sym.owner != ownerTpe.typeSymbol, NoSymbol)
    members.allMembers #:: {
      //print("\nadd pimped")
      val applicableViews: List[SearchResult] =
        if (ownerTpe.isErroneous) List()
        else new ImplicitSearch(
          tree, functionType(List(ownerTpe), AnyClass.tpe), isView = true,
          context0 = context.makeImplicit(reportAmbiguousErrors = false)).allImplicits
      for (view <- applicableViews) {
        val vtree = viewApply(view)
        val vpre = stabilizedType(vtree)
        for (sym <- vtree.tpe.members) {
          addTypeMember(sym, vpre, false, view.tree.symbol)
        }
      }
      //println()
      Stream(members.allMembers)
    }
  }

}
