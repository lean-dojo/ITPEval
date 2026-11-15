;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_296: every natural number at least 2 that is both a
;; perfect cube and a perfect fourth power is at least 4096. This file
;; contains no proof.

(in-package "ACL2")

;; For a positive exponent, a natural power witness for radicand n cannot
;; exceed n. Thus, in the statement below, searching from n down to 0 is
;; equivalent to the source existential quantifier over all natural numbers.
(defun mathd-numbertheory-296-power-witness-through-p
    (radicand exponent candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (natp candidate)
      (or (equal (expt candidate exponent) radicand)
          (and (not (zp candidate))
               (mathd-numbertheory-296-power-witness-through-p
                radicand exponent (- candidate 1))))
    nil))

(defun mathd-numbertheory-296-statement (n)
  (implies
   (and (natp n)
        (<= 2 n)
        (mathd-numbertheory-296-power-witness-through-p n 3 n)
        (mathd-numbertheory-296-power-witness-through-p n 4 n))
   (<= 4096 n)))

(value-triple :itpeval-statement-checked)
:q
