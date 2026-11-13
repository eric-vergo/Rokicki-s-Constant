-- Vendored from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
-- (commit c39a751132c88b6e8080b74c74023fd95b3d8be0, file `PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean`)
-- by `scripts/vendor-pnt.py`: unchanged. Do not edit; see `vendor/README.md`.
import Mathlib.Algebra.Notation.Support

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function
