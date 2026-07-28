/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

import ProofNet.ForMathlib.Partition.Orthogonality
import ProofNet.Formula
import ProofNet.Vorspeil.Term

/-! Connectives and switchings -/

namespace GMLL

structure Connective where
  ar : ℕ
  rules : Set (Partition (Set.univ : Set (Fin ar)))

end GMLL

namespace MLL

variable {Atom : Type*}

end MLL
