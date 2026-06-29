 ============================================================
 Translations of theorem statements from Validity2.agda
 ------------------------------------------------------------

Translation conventions (Agda → Rocq):
     FinMem u a              ≈  wt u a
     FinMem b UCode          ≈  wt b tuniv              (some i)
     Coherent u              ≈  valid u                 (implicit in wt)
     CoherentFun g           ≈  valid_fun g /\ g <> nil (implicit in wt (abs g) ..)
     CoherentFunTail f       ≈  valid_fun f             (implicit in wt (tpi _ f) ..)
     FinMemFun g b f         ≈  wt (abs g) (tpi b f)
     FinMemAllU f b          ≈  wt (tpi b f) tuniv (codomains in U_i)
     LeCode u v              ≈  le u v
     LeFunCode f g           ≈  le_fun f g
     Comp u v                ≈  compatible u v
     Sup u v = w             ≈  lub u v = w
     EvalFun f u = v         ≈  app f u = v
     subst1 B N              ≈  B[N..]
     HasType / ConvTm        ≈  typing / conv
     HeadRed                 ≈  HeadRed (multi reduction)
     FinEl                 elt
     FinFun                list (elt * elt)
     Bot / Sup u v         bot / lub u v
     FinMem-Sup-element     wt_lub
