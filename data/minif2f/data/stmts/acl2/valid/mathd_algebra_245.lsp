;; Statement-only formalization of miniF2F artifact mathd_algebra_245:
;; for every nonzero real x, the source product of reciprocal powers is
;; equal to 18*x^8. This file contains no proof.
;;
;; ACL2 has no native real field. The explicit field carrier below preserves
;; the arbitrary source variable, every division and inverse, and all powers
;; directly. The identity is valid in every field and hence in the reals.
;; Every field law is a premise; none encodes the cancellation result.

(in-package "ACL2")

(set-inhibit-output-lst '(proof-tree prove observation))

(defstub mathd245-real-p (value) t)
(defstub mathd245-zero () t)
(defstub mathd245-one () t)
(defstub mathd245-add (left right) t)
(defstub mathd245-mul (left right) t)
(defstub mathd245-neg (value) t)
(defstub mathd245-inv (value) t)

(defun mathd245-div (left right)
  (mathd245-mul left (mathd245-inv right)))

(defun mathd245-natural (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (mathd245-zero)
    (mathd245-add
     (mathd245-one)
     (mathd245-natural (1- n)))))

(defun mathd245-pow2 (value)
  (mathd245-mul value value))

(defun mathd245-pow3 (value)
  (mathd245-mul (mathd245-pow2 value) value))

(defun mathd245-pow4 (value)
  (mathd245-pow2 (mathd245-pow2 value)))

(defun mathd245-pow8 (value)
  (mathd245-pow2 (mathd245-pow4 value)))

(defun-sk mathd245-field-laws-p ()
  (forall
   (x y z)
   (and
    (implies
     (and (mathd245-real-p x)
          (mathd245-real-p y))
     (and
      (mathd245-real-p (mathd245-add x y))
      (mathd245-real-p (mathd245-mul x y))))
    (implies
     (mathd245-real-p x)
     (and
      (mathd245-real-p (mathd245-neg x))
      (mathd245-real-p (mathd245-inv x))))
    (implies
     (and
      (mathd245-real-p x)
      (mathd245-real-p y)
      (mathd245-real-p z))
     (equal
      (mathd245-add (mathd245-add x y) z)
      (mathd245-add x (mathd245-add y z))))
    (implies
     (and (mathd245-real-p x)
          (mathd245-real-p y))
     (equal (mathd245-add x y)
            (mathd245-add y x)))
    (implies
     (mathd245-real-p x)
     (and
      (equal (mathd245-add x (mathd245-zero)) x)
      (equal
       (mathd245-add x (mathd245-neg x))
       (mathd245-zero))))
    (implies
     (and
      (mathd245-real-p x)
      (mathd245-real-p y)
      (mathd245-real-p z))
     (equal
      (mathd245-mul (mathd245-mul x y) z)
      (mathd245-mul x (mathd245-mul y z))))
    (implies
     (and (mathd245-real-p x)
          (mathd245-real-p y))
     (equal (mathd245-mul x y)
            (mathd245-mul y x)))
    (implies
     (mathd245-real-p x)
     (equal (mathd245-mul x (mathd245-one)) x))
    (implies
     (and
      (mathd245-real-p x)
      (not (equal x (mathd245-zero))))
     (equal
      (mathd245-mul x (mathd245-inv x))
      (mathd245-one)))
    (equal (mathd245-inv (mathd245-zero))
           (mathd245-zero))
    (implies
     (and
      (mathd245-real-p x)
      (mathd245-real-p y)
      (mathd245-real-p z))
     (equal
      (mathd245-mul x (mathd245-add y z))
      (mathd245-add
       (mathd245-mul x y)
       (mathd245-mul x z)))))))

(defun mathd245-field-p ()
  (and
   (mathd245-real-p (mathd245-zero))
   (mathd245-real-p (mathd245-one))
   (not (equal (mathd245-zero)
               (mathd245-one)))
   (mathd245-field-laws-p)))

(defun-sk mathd-algebra-245-statement-p ()
  (forall
   (x)
   (implies
    (and
     (mathd245-field-p)
     (mathd245-real-p x)
     (not (equal x (mathd245-zero))))
    (equal
     (mathd245-mul
      (mathd245-mul
       (mathd245-inv
        (mathd245-div (mathd245-natural 4) x))
       (mathd245-pow2
        (mathd245-div
         (mathd245-mul
          (mathd245-natural 3)
          (mathd245-pow3 x))
         x)))
      (mathd245-pow3
       (mathd245-inv
        (mathd245-div
         (mathd245-one)
         (mathd245-mul
          (mathd245-natural 2)
          x)))))
     (mathd245-mul
      (mathd245-natural 18)
      (mathd245-pow8 x))))))

(value-triple :itpeval-statement-checked)
:q
