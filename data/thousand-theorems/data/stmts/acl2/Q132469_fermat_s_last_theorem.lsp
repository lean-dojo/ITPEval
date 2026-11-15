;; Statement-only formalization of thousand-theorems corpus artifact Q132469,
;; "Fermat's Last Theorem": for every natural exponent at least 3, no three
;; nonzero natural numbers satisfy a^n + b^n = c^n. This file contains no proof.

(in-package "ACL2")

(defun-sk thousand-theorems-q132469-fermat-last-theorem-statement ()
  (forall (n a b c)
    (implies
     (and (natp n)
          (<= 3 n)
          (natp a)
          (natp b)
          (natp c)
          (not (equal a 0))
          (not (equal b 0))
          (not (equal c 0)))
     (not
      (equal (+ (expt a n)
                (expt b n))
             (expt c n))))))

(value-triple :itpeval-statement-checked)
:q
