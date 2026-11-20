import Tamarin.DHPeer
import Tamarin.TableAmbient

/-! Read and lift the five declared DH operators from a numeric dictionary. -/
namespace Tamarin.DHWire
open Rewriting DHPeer TotalUnifyWire

/-- Check the declarations chosen for the five operators in a packet dictionary. -/
def readSymbols {d : Dictionary} (pow inv one neutral : d.sig.FreeSym) (mul : d.sig.ACSym) :
    Option (Symbols d.sig) :=
  if h : d.sig.arity pow = 2 ∧ d.sig.arity inv = 1 ∧ d.sig.arity one = 0 ∧ d.sig.arity neutral = 0 ∧
      (∀ i, d.sig.inputSort pow i = .msg) ∧ (∀ i, d.sig.inputSort inv i = .msg) ∧
      d.sig.outputSort pow = .msg ∧ d.sig.outputSort inv = .msg ∧ d.sig.outputSort one = .msg ∧
      d.sig.outputSort neutral = .msg ∧ d.sig.acSort mul = .msg then
    some (by obtain ⟨a,b,c,e,f,g,i,j,k,l,m⟩ := h; exact ⟨pow,inv,one,neutral,mul,a,b,c,e,f,g,i,j,k,l,m⟩)
  else none

def liftSymbols {d : Dictionary} (s : Symbols d.sig) : Symbols (TableAmbient.sig d) :=
  ⟨.inl s.pow,.inl s.inv,.inl s.one,.inl s.neutral,.inl s.mul,
   s.powArity,s.invArity,s.oneArity,s.neutralArity,s.powInput,s.invInput,s.powSort,s.invSort,
   s.oneSort,s.neutralSort,s.mulSort⟩

end Tamarin.DHWire
