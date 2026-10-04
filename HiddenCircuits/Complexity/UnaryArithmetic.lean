import HiddenCircuits.Complexity.OracleRepeat

/-! Operational unary arithmetic for polynomially bounded emitter dimensions and
indices. These routines are never used for exponentially large oracle values. -/
namespace HiddenCircuits.Complexity.OracleBlock
variable {k : ℕ}

noncomputable def repeatCopy (counter source target temporary : Fin (k+1))
    (hst : source ≠ target) (hsu : source ≠ temporary) (htu : target ≠ temporary) : OracleBlock k :=
  whilePop counter (copyOn source target temporary hst hsu htu) (copyOn source target temporary hst hsu htu)

/-- Repeated actual copying consumes the counter, preserves the source and all
work tapes, and appends exactly counter.length copies to the target. -/
theorem repeatCopy_executes (g : BitString → ℕ) (counter source target temporary : Fin (k+1))
    (hcs : counter ≠ source) (hct : counter ≠ target) (hcu : counter ≠ temporary)
    (hst : source ≠ target) (hsu : source ≠ temporary) (htu : target ≠ temporary)
    (s : Store k) (hzero : s temporary = []) :
    (repeatCopy counter source target temporary hst hsu htu).Executes g s
      (workStore s counter target [] ((List.replicate (s counter).length (s source)).flatten++s target))
      ((5*(s source).length+4)*(s counter).length+1) := by
  have hb (rest acc : BitString) : (copyOn source target temporary hst hsu htu).Executes g
      (workStore s counter target rest acc) (workStore s counter target rest (s source++acc))
      (5*(s source).length+2) := by
    have hz : workStore s counter target rest acc temporary = [] := by
      simp [workStore,Ne.symm hcu,Ne.symm htu,hzero]
    simpa [workStore,hst,Ne.symm hcs] using
      copyOn_executes g source target temporary hst hsu htu (workStore s counter target rest acc) hz
  have hi := whilePrepend_execution g counter target hct (copyOn source target temporary hst hsu htu)
    (s source) (5*(s source).length+2) s hb (s counter) (s target)
  have h := whilePop_executes counter _ _ g hi
  simpa [workStore] using h

lemma repeatCopy_queryFree (counter source target temporary : Fin (k+1))
    (hst : source ≠ target) (hsu : source ≠ temporary) (htu : target ≠ temporary) :
    (repeatCopy counter source target temporary hst hsu htu).QueryFree :=
  whilePop_queryFree _ _ _ (copyOn_queryFree _ _ _ _ _ _) (copyOn_queryFree _ _ _ _ _ _)

/-- Multiplication by physically repeating a unary source. This preserves the
source, consumes the unary counter, and supports an arbitrary target suffix. -/
theorem unaryMultiply_executes (g : BitString → ℕ) (counter source target temporary : Fin (k+1))
    (hcs : counter ≠ source) (hct : counter ≠ target) (hcu : counter ≠ temporary)
    (hst : source ≠ target) (hsu : source ≠ temporary) (htu : target ≠ temporary)
    (s : Store k) (a b : ℕ) (ha : s counter = List.replicate a true)
    (hb : s source = List.replicate b true) (hzero : s temporary = []) :
    (repeatCopy counter source target temporary hst hsu htu).Executes g s
      (workStore s counter target [] (List.replicate (a*b) true++s target)) ((5*b+4)*a+1) := by
  simpa [ha,hb] using repeatCopy_executes g counter source target temporary hcs hct hcu hst hsu htu s hzero

end HiddenCircuits.Complexity.OracleBlock
