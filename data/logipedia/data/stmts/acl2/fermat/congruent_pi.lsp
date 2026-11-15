;; Statement-only formalization of Logipedia corpus artifact
;; fermat.congruent_pi, catalog title "fermat.congruent_pi": for every
;; natural-valued function and positive natural modulus, the product of its
;; values at indices below a natural bound is congruent modulo the modulus to
;; the product of their individual remainders. This file contains no proof.

(in-package "ACL2")

(defstub logipedia-fermat-congruent-pi-f (index) t)

(defun-sk logipedia-fermat-congruent-pi-natural-function-p ()
  (forall (index)
    (implies (natp index)
             (natp (logipedia-fermat-congruent-pi-f index)))))

(defun logipedia-fermat-congruent-pi-product (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* (logipedia-fermat-congruent-pi-f (- n 1))
       (logipedia-fermat-congruent-pi-product (- n 1)))))

(defun logipedia-fermat-congruent-pi-remainder-product (n p)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* (mod (logipedia-fermat-congruent-pi-f (- n 1)) p)
       (logipedia-fermat-congruent-pi-remainder-product (- n 1) p))))

(defun logipedia-fermat-congruent-pi-statement (n p)
  (implies
    (and (logipedia-fermat-congruent-pi-natural-function-p)
         (natp n)
         (natp p)
         (< 0 p))
    (equal
      (mod (logipedia-fermat-congruent-pi-product n) p)
      (mod (logipedia-fermat-congruent-pi-remainder-product n p) p))))

(value-triple :itpeval-statement-checked)

:q
