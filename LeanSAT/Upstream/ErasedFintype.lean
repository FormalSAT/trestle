import Mathlib.Data.Erased
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Fin

class ErasedFintype (α : Type u) where
  val : Erased (Fintype α)

namespace ErasedFintype

noncomputable def toFintype [ErasedFintype α] : Fintype α := ErasedFintype.val.out

instance [Fintype α] : ErasedFintype α where
  val := .mk inferInstance

instance [ErasedFintype α] [ErasedFintype β] : ErasedFintype (α × β) where
  val :=
    have : Fintype α := toFintype
    have : Fintype β := toFintype
    .mk inferInstance

instance [ErasedFintype α] [ErasedFintype β] : ErasedFintype (α ⊕ β) where
  val :=
    have : Fintype α := toFintype
    have : Fintype β := toFintype
    .mk inferInstance

instance : ErasedFintype (Fin n) := inferInstance
