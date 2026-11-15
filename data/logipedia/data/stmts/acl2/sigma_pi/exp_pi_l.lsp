;; Statement-only formalization of Logipedia corpus artifact sigma_pi.exp_pi_l,
;; catalog title "sigma_pi.exp_pi_l": distributing a natural power across a
;; finite product of values of an arbitrary natural-valued function.
;; This file contains no proof.

(in-package "ACL2")

;; This conservative interface represents the source's universally quantified
;; function f : nat -> nat.
(defstub logipedia-sigma-pi-exp-pi-l-f (index) t)

(defun-sk logipedia-sigma-pi-exp-pi-l-f-typed-p ()
  (forall (index)
    (implies
     (natp index)
     (natp (logipedia-sigma-pi-exp-pi-l-f index)))))

(defun logipedia-sigma-pi-exp-pi-l-product (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      1
    (* (logipedia-sigma-pi-exp-pi-l-f (1- count))
       (logipedia-sigma-pi-exp-pi-l-product (1- count)))))

(defun logipedia-sigma-pi-exp-pi-l-scaled-product (count scale)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      1
    (* (* scale
          (logipedia-sigma-pi-exp-pi-l-f (1- count)))
       (logipedia-sigma-pi-exp-pi-l-scaled-product
        (1- count) scale))))

(defun-sk logipedia-sigma-pi-exp-pi-l-statement ()
  (forall (n a)
    (implies
     (and
      (natp n)
      (natp a)
      (logipedia-sigma-pi-exp-pi-l-f-typed-p))
     (equal
      (* (expt a n)
         (logipedia-sigma-pi-exp-pi-l-product n))
      (logipedia-sigma-pi-exp-pi-l-scaled-product n a)))))

(value-triple :itpeval-statement-checked)
:q
