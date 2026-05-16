import ProofNet.Partition.Orthogonality

namespace GMLL

structure Connective where
  ar : ℕ
  rules : Set (Partition (Set.univ : Set (Fin ar)))



end GMLL
