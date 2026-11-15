;; Statement-only formalization of miniF2F corpus artifact aime_1988_p8:
;; every real-valued function on pairs of natural numbers satisfying the
;; stated diagonal, symmetry, and functional equations has f(14,52) = 364.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative symbols present an arbitrary Archimedean ordered field and an
;; arbitrary binary function.  The carrier and function are unbounded: no
;; finite table, rational surrogate, or bounded quantifier is used.  This is
;; equivalent to the real-valued source statement because every Archimedean
;; ordered field embeds in the reals, while the countable subfield generated
;; by the values of any source function supplies a presentation in this form.

(defstub aime-1988-p8-real-p (value) t)
(defstub aime-1988-p8-zero () t)
(defstub aime-1988-p8-one () t)
(defstub aime-1988-p8-add (left right) t)
(defstub aime-1988-p8-multiply (left right) t)
(defstub aime-1988-p8-negate (value) t)
(defstub aime-1988-p8-inverse (value) t)
(defstub aime-1988-p8-less (left right) t)
(defstub aime-1988-p8-f (x y) t)

(defun aime-1988-p8-natural (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (aime-1988-p8-zero)
    (aime-1988-p8-add
     (aime-1988-p8-one)
     (aime-1988-p8-natural (1- n)))))

(defun-sk aime-1988-p8-field-laws-p ()
  (forall (x y z)
    (implies
     (and (aime-1988-p8-real-p x)
          (aime-1988-p8-real-p y)
          (aime-1988-p8-real-p z))
     (and
      (aime-1988-p8-real-p
       (aime-1988-p8-add x y))
      (aime-1988-p8-real-p
       (aime-1988-p8-multiply x y))
      (aime-1988-p8-real-p
       (aime-1988-p8-negate x))
      (aime-1988-p8-real-p
       (aime-1988-p8-inverse x))
      (equal
       (aime-1988-p8-add
        (aime-1988-p8-add x y)
        z)
       (aime-1988-p8-add
        x
        (aime-1988-p8-add y z)))
      (equal
       (aime-1988-p8-add x y)
       (aime-1988-p8-add y x))
      (equal
       (aime-1988-p8-add x (aime-1988-p8-zero))
       x)
      (equal
       (aime-1988-p8-add x (aime-1988-p8-negate x))
       (aime-1988-p8-zero))
      (equal
       (aime-1988-p8-multiply
        (aime-1988-p8-multiply x y)
        z)
       (aime-1988-p8-multiply
        x
        (aime-1988-p8-multiply y z)))
      (equal
       (aime-1988-p8-multiply x y)
       (aime-1988-p8-multiply y x))
      (equal
       (aime-1988-p8-multiply x (aime-1988-p8-one))
       x)
      (implies
       (not (equal x (aime-1988-p8-zero)))
       (equal
        (aime-1988-p8-multiply
         x
         (aime-1988-p8-inverse x))
        (aime-1988-p8-one)))
      (equal
       (aime-1988-p8-multiply
        x
        (aime-1988-p8-add y z))
       (aime-1988-p8-add
        (aime-1988-p8-multiply x y)
        (aime-1988-p8-multiply x z)))))))

(defun-sk aime-1988-p8-order-laws-p ()
  (forall (x y z)
    (implies
     (and (aime-1988-p8-real-p x)
          (aime-1988-p8-real-p y)
          (aime-1988-p8-real-p z))
     (and
      (not (aime-1988-p8-less x x))
      (or (equal x y)
          (aime-1988-p8-less x y)
          (aime-1988-p8-less y x))
      (implies
       (and (aime-1988-p8-less x y)
            (aime-1988-p8-less y z))
       (aime-1988-p8-less x z))
      (implies
       (aime-1988-p8-less x y)
       (aime-1988-p8-less
        (aime-1988-p8-add x z)
        (aime-1988-p8-add y z)))
      (implies
       (and
        (aime-1988-p8-less (aime-1988-p8-zero) x)
        (aime-1988-p8-less (aime-1988-p8-zero) y))
       (aime-1988-p8-less
        (aime-1988-p8-zero)
        (aime-1988-p8-multiply x y)))))))

(defun-sk aime-1988-p8-natural-bound-exists-p (x)
  (exists (n)
    (and
     (natp n)
     (aime-1988-p8-less
      x
      (aime-1988-p8-natural n)))))

(defun-sk aime-1988-p8-archimedean-p ()
  (forall (x)
    (implies
     (aime-1988-p8-real-p x)
     (aime-1988-p8-natural-bound-exists-p x))))

(defun aime-1988-p8-real-field-p ()
  (and
   (aime-1988-p8-real-p (aime-1988-p8-zero))
   (aime-1988-p8-real-p (aime-1988-p8-one))
   (not (equal (aime-1988-p8-zero)
               (aime-1988-p8-one)))
   (aime-1988-p8-less
    (aime-1988-p8-zero)
    (aime-1988-p8-one))
   (aime-1988-p8-field-laws-p)
   (aime-1988-p8-order-laws-p)
   (aime-1988-p8-archimedean-p)))

(defun-sk aime-1988-p8-real-valued-p ()
  (forall (x y)
    (implies
     (and (natp x)
          (natp y))
     (aime-1988-p8-real-p
      (aime-1988-p8-f x y)))))

(defun-sk aime-1988-p8-diagonal-p ()
  (forall (x)
    (implies
     (posp x)
     (equal
      (aime-1988-p8-f x x)
      (aime-1988-p8-natural x)))))

(defun-sk aime-1988-p8-symmetric-p ()
  (forall (x y)
    (implies
     (and (posp x)
          (posp y))
     (equal
      (aime-1988-p8-f x y)
      (aime-1988-p8-f y x)))))

(defun-sk aime-1988-p8-functional-equation-p ()
  (forall (x y)
    (implies
     (and (posp x)
          (posp y))
     (equal
      (aime-1988-p8-multiply
       (aime-1988-p8-natural (+ x y))
       (aime-1988-p8-f x y))
      (aime-1988-p8-multiply
       (aime-1988-p8-natural y)
       (aime-1988-p8-f x (+ x y)))))))

(defun aime-1988-p8-statement ()
  (implies
   (and
    (aime-1988-p8-real-field-p)
    (aime-1988-p8-real-valued-p)
    (aime-1988-p8-diagonal-p)
    (aime-1988-p8-symmetric-p)
    (aime-1988-p8-functional-equation-p))
   (equal
    (aime-1988-p8-f 14 52)
    (aime-1988-p8-natural 364))))

(value-triple :itpeval-statement-checked)
:q
