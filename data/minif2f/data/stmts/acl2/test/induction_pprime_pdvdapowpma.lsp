;; Statement-only formalization of miniF2F corpus artifact
;; induction_pprime_pdvdapowpma: for positive natural a and prime natural p,
;; p divides the truncated natural difference a^p - a. This file contains no
;; proof.

(in-package "ACL2")

(defun induction-pprime-pdvdapowpma-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and (not (equal (mod n d) 0))
           (induction-pprime-pdvdapowpma-no-divisor-from-p n (+ d 1)))
    t))

(defun induction-pprime-pdvdapowpma-primep (n)
  (and (natp n)
       (< 1 n)
       (induction-pprime-pdvdapowpma-no-divisor-from-p n 2)))

(defun induction-pprime-pdvdapowpma-statement (p a)
  (implies
   (and (natp p)
        (natp a)
        (< 0 a)
        (induction-pprime-pdvdapowpma-primep p))
   (equal (mod (nfix (- (expt a p) a)) p)
          0)))

(value-triple :itpeval-statement-checked)
:q
