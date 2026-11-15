;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__033, "Fermat's Last Theorem": for every natural
;; exponent n greater than 2 and positive natural numbers a, b, and c,
;; a^n + b^n is not equal to c^n. This file contains no proof.

(in-package "ACL2")

(defun hundred-theorems-033-fermat-last-theorem-statement (n a b c)
  (implies
   (and (natp n)
        (< 2 n)
        (natp a)
        (< 0 a)
        (natp b)
        (< 0 b)
        (natp c)
        (< 0 c))
   (not (equal (+ (expt a n)
                  (expt b n))
               (expt c n)))))

(value-triple :itpeval-statement-checked)
:q
