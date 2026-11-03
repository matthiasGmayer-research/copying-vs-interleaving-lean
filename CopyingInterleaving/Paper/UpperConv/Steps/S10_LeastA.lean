import CopyingInterleaving.Paper.UpperConv.Defs

/-! Target `UpperConv`: proof of lem-least, part (a) (main.typ 505–507). -/

namespace CopyingInterleaving.Paper.UpperConv

open CopyingInterleaving.Paper.Prelim

/-- main.typ 505–507, proof of lem-least, part (a) (one paragraph, no steps). Claim = lem-least (a)
(main.typ 493–495): "Let `ρ ∈ occ_v`, and let `ζ ∈ occ_z` be the occurrence along a prefix of its root
path, ending at `z`. Then `ρ(t) = ζ(pt + b)` for all `t`, where `p` is the product of the rest of the path
(from `z` to `v`) and `b ≥ 0` is an integer; and if `ρ` is lowest at `t`, then `ζ` is lowest at `pt + b`."
(The root path of `ρ` is `js₁ ++ js₂`, the prefix `js₁` ends at `z`, the rest is `js₂`.) -/
theorem step_lem_least_a {Q α : Type} (P : Program Q α) (hP : IsZLP P) (v z : Q) (ρ ζ : Occ)
    (js₁ js₂ : List ℕ) (hρ : OccVia P v ρ (js₁ ++ js₂)) (hζ : OccVia P z ζ js₁) :
    ∃ b : ℕ, (∀ t : ℕ, ρ t = ζ (pathProduct P z js₂ * t + b)) ∧
      ∀ t : ℕ, IsLowest P v ρ t → IsLowest P z ζ (pathProduct P z js₂ * t + b) := by
  have hf₁ : P.follow (.inl P.root) js₁ = some (.inl z) := P.follow_of_occVia hζ
  have hρe : ρ = ζ.comp (P.pathOcc z js₂) := by
    rw [P.eq_pathOcc_of_occVia hζ, P.eq_pathOcc_of_occVia hρ, SlotGraph.pathOcc_append _ hf₁]
  have hfz : P.follow (.inl z) js₂ = some (.inl v) := by
    have hf := P.follow_of_occVia hρ
    rw [SlotGraph.follow_append, hf₁] at hf
    simpa using hf
  have hstep : (P.pathOcc z js₂).step = pathProduct P z js₂ :=
    SlotGraph.pathOcc_step _ z js₂
  have hrel : ∀ t : ℕ, ρ t = ζ (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset) := by
    intro t
    rw [hρe, Occ.comp_apply]
    show ζ ((P.pathOcc z js₂).step * t + (P.pathOcc z js₂).offset) = _
    rw [hstep]
  refine ⟨(P.pathOcc z js₂).offset, hrel, fun t ht => ?_⟩
  unfold IsLowest at ht ⊢
  have hne : ((fun η : Occ => η (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset)) ''
      P.occ z).Nonempty :=
    ⟨_, ζ, ⟨js₁, hζ⟩, rfl⟩
  obtain ⟨η, ⟨js', hη⟩, hηs⟩ := Nat.sInf_mem hne
  refine le_antisymm ?_ (Nat.sInf_le ⟨ζ, ⟨js₁, hζ⟩, rfl⟩)
  by_contra hlt
  have hlt' : firstPos P z (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset) <
      ζ (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset) := not_le.mp hlt
  have hηs' : η (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset) =
      firstPos P z (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset) := hηs
  have hfη := P.follow_of_occVia hη
  have hηe := P.eq_pathOcc_of_occVia hη
  have hfv : P.follow (.inl P.root) (js' ++ js₂) = some (.inl v) := by
    rw [SlotGraph.follow_append, hfη]
    simpa using hfz
  have hρ'occ : P.pathOcc P.root (js' ++ js₂) ∈ P.occ v :=
    ⟨js' ++ js₂, P.occVia_iff.mpr ⟨hfv, rfl⟩⟩
  have hρ'eq : P.pathOcc P.root (js' ++ js₂) = η.comp (P.pathOcc z js₂) := by
    rw [hηe, SlotGraph.pathOcc_append _ hfη]
  have hval : P.pathOcc P.root (js' ++ js₂) t =
      η (pathProduct P z js₂ * t + (P.pathOcc z js₂).offset) := by
    rw [hρ'eq, Occ.comp_apply]
    show η ((P.pathOcc z js₂).step * t + (P.pathOcc z js₂).offset) = _
    rw [hstep]
  have hlow : firstPos P v t ≤ P.pathOcc P.root (js' ++ js₂) t :=
    Nat.sInf_le ⟨_, hρ'occ, rfl⟩
  have hρt := hrel t
  omega

end CopyingInterleaving.Paper.UpperConv
