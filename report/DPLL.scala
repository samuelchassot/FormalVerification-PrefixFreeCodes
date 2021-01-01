def DPLL(S: Set[Clause]) : $\BB$ =
  val S' = subsumption(UnitProp(S))
  if $\emptyset$ $\in$ S' then false // unsat
  else if S' has only unit clauses then true // unit clauses give e
  else
     val L = a literal from a clause of S' where {L} $\notin$ S'
     DPLL(S' $\cup$ {{L}}) || DPLL(S' $\cup$ {{complement(L)}})

def UnitProp(S: Set[Clause]): Set[Clause] = // Unit Propagation (BCP)
  if C $\in$ S, unit U $\in S$, resolve(U,C) $\notin$ S
  then UnitProp((S - {C}) $\cup$ {resolve(U,C)}) else S

def subsumption(S: Set[Clause]): Set[Clause] =
  if C1,C2 $\in$ S such that C1 $\subseteq$ C2 
  then subsumption(S - {C2})  else S