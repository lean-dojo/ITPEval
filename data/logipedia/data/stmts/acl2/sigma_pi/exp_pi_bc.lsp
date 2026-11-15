;; Statement-only formalization of Logipedia corpus artifact sigma_pi.exp_pi_bc,
;; catalog title "sigma_pi.exp_pi_bc": distributing a natural power across a
;; finite product of values of an arbitrary natural-valued function.
;; This file contains no proof.

(in-package "ACL2")

;; This conservative interface represents the source's universally quantified
;; function f : nat -> nat.
(defstub logipedia-sigma-pi-exp-pi-bc-f (index) t)

(defun-sk logipedia-sigma-pi-exp-pi-bc-f-typed-p ()
  (forall (index)
    (implies
     (natp index)
     (natp (logipedia-sigma-pi-exp-pi-bc-f index)))))

(defun logipedia-sigma-pi-exp-pi-bc-product (count offset)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      1
    (* (logipedia-sigma-pi-exp-pi-bc-f
        (+ (1- count) offset))
       (logipedia-sigma-pi-exp-pi-bc-product
        (1- count) offset))))

(defun logipedia-sigma-pi-exp-pi-bc-scaled-product
    (count offset scale)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      1
    (* (* scale
          (logipedia-sigma-pi-exp-pi-bc-f
           (+ (1- count) offset)))
       (logipedia-sigma-pi-exp-pi-bc-scaled-product
        (1- count) offset scale))))

(defun-sk logipedia-sigma-pi-exp-pi-bc-statement ()
  (forall (a b c)
    (implies
     (and
      (natp a)
      (natp b)
      (natp c)
      (logipedia-sigma-pi-exp-pi-bc-f-typed-p))
     (let ((count (nfix (- c b))))
       (equal
        (* (expt a count)
           (logipedia-sigma-pi-exp-pi-bc-product count b))
        (logipedia-sigma-pi-exp-pi-bc-scaled-product
         count b a))))))

(value-triple :itpeval-statement-checked)
:q
