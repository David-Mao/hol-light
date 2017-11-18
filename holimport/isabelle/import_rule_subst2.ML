Alternate version of subst; One generalize+instantiate as opposed to repeated forall; still slower.

fun subst cplst th =
  let
    val thy = @{theory};
    val idx = Thm.maxidx_of th;
    val (slst, tlst) = ListPair.unzip cplst;
    val lnames = map (fst o dest_Free o term_of) slst;
    val th2 = Thm.generalize ([], lnames) (idx + 1) th;
    val vars = Term.add_vars (concl_of th2) [];
    val aslst = ListPair.zip (lnames, tlst);
    fun mk_pair (((n, i), ty)) =
      (cterm_of thy (Var ((n,i),ty)), Option.valOf (AList.lookup (op =) aslst n))
    val sbst = map mk_pair vars
  in
    Thm.instantiate ([], sbst) th2
  end
