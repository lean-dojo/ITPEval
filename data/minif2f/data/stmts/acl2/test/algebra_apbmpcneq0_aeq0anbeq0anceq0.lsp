;; Statement-only formalization of miniF2F artifact
;; algebra_apbmpcneq0_aeq0anbeq0anceq0: if positive reals m and n have
;; cubes 2 and 4, then every rational linear relation
;; a + b*m + c*n = 0 has a = b = c = 0. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 has no built-in first-class real field. The arbitrary carrier below
;; keeps m and n independent of any coordinate basis; all ordered-field and
;; rational-embedding laws remain explicit theorem premises.

(defstub apbmpc-real-p (real-type value) t)
(defstub apbmpc-zero (real-type) t)
(defstub apbmpc-one (real-type) t)
(defstub apbmpc-add (real-type left right) t)
(defstub apbmpc-mul (real-type left right) t)
(defstub apbmpc-neg (real-type value) t)
(defstub apbmpc-inv (real-type value) t)
(defstub apbmpc-le (real-type left right) t)
(defstub apbmpc-of-rational (real-type rational) t)

(defun apbmpc-lt (real-type x y)
  (and
   (apbmpc-le real-type x y)
   (not (equal x y))))

(defun apbmpc-cube (real-type x)
  (apbmpc-mul
   real-type
   x
   (apbmpc-mul real-type x x)))

(defun-sk apbmpc-closure-laws-p (real-type)
  (forall (x y)
    (and
     (apbmpc-real-p real-type (apbmpc-zero real-type))
     (apbmpc-real-p real-type (apbmpc-one real-type))
     (implies
      (apbmpc-real-p real-type x)
      (and
       (apbmpc-real-p real-type (apbmpc-neg real-type x))
       (apbmpc-real-p real-type (apbmpc-inv real-type x))))
     (implies
      (and
       (apbmpc-real-p real-type x)
       (apbmpc-real-p real-type y))
      (and
       (apbmpc-real-p real-type (apbmpc-add real-type x y))
       (apbmpc-real-p real-type (apbmpc-mul real-type x y)))))))

(defun-sk apbmpc-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (apbmpc-real-p real-type x)
      (apbmpc-real-p real-type y)
      (apbmpc-real-p real-type z))
     (let ((zero (apbmpc-zero real-type))
           (one (apbmpc-one real-type)))
       (and
        (not (equal zero one))
        (equal
         (apbmpc-add real-type x y)
         (apbmpc-add real-type y x))
        (equal
         (apbmpc-add real-type (apbmpc-add real-type x y) z)
         (apbmpc-add real-type x (apbmpc-add real-type y z)))
        (equal (apbmpc-add real-type x zero) x)
        (equal
         (apbmpc-add real-type x (apbmpc-neg real-type x))
         zero)
        (equal
         (apbmpc-mul real-type x y)
         (apbmpc-mul real-type y x))
        (equal
         (apbmpc-mul real-type (apbmpc-mul real-type x y) z)
         (apbmpc-mul real-type x (apbmpc-mul real-type y z)))
        (equal (apbmpc-mul real-type x one) x)
        (equal
         (apbmpc-mul
          real-type
          x
          (apbmpc-add real-type y z))
         (apbmpc-add
          real-type
          (apbmpc-mul real-type x y)
          (apbmpc-mul real-type x z)))
        (implies
         (not (equal x zero))
         (equal
          (apbmpc-mul real-type x (apbmpc-inv real-type x))
          one)))))))

(defun-sk apbmpc-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (apbmpc-real-p real-type x)
      (apbmpc-real-p real-type y)
      (apbmpc-real-p real-type z))
     (let ((zero (apbmpc-zero real-type)))
       (and
        (apbmpc-le real-type x x)
        (implies
         (and
          (apbmpc-le real-type x y)
          (apbmpc-le real-type y x))
         (equal x y))
        (implies
         (and
          (apbmpc-le real-type x y)
          (apbmpc-le real-type y z))
         (apbmpc-le real-type x z))
        (or
         (apbmpc-le real-type x y)
         (apbmpc-le real-type y x))
        (implies
         (apbmpc-le real-type x y)
         (apbmpc-le
          real-type
          (apbmpc-add real-type x z)
          (apbmpc-add real-type y z)))
        (implies
         (and
          (apbmpc-le real-type zero x)
          (apbmpc-le real-type zero y))
         (apbmpc-le
          real-type
          zero
          (apbmpc-mul real-type x y))))))))

(defun-sk apbmpc-rational-laws-p (real-type)
  (forall (p q)
    (implies
     (and (rationalp p) (rationalp q))
     (and
      (apbmpc-real-p
       real-type (apbmpc-of-rational real-type p))
      (equal
       (apbmpc-of-rational real-type 0)
       (apbmpc-zero real-type))
      (equal
       (apbmpc-of-rational real-type 1)
       (apbmpc-one real-type))
      (equal
       (apbmpc-of-rational real-type (+ p q))
       (apbmpc-add
        real-type
        (apbmpc-of-rational real-type p)
        (apbmpc-of-rational real-type q)))
      (equal
       (apbmpc-of-rational real-type (* p q))
       (apbmpc-mul
        real-type
        (apbmpc-of-rational real-type p)
        (apbmpc-of-rational real-type q)))
      (equal
       (apbmpc-of-rational real-type (- p))
       (apbmpc-neg
        real-type
        (apbmpc-of-rational real-type p)))
      (iff
       (equal p q)
       (equal
        (apbmpc-of-rational real-type p)
        (apbmpc-of-rational real-type q)))
      (iff
       (<= p q)
       (apbmpc-le
        real-type
        (apbmpc-of-rational real-type p)
        (apbmpc-of-rational real-type q)))))))

(defun apbmpc-real-structure-p (real-type)
  (and
   (apbmpc-closure-laws-p real-type)
   (apbmpc-field-laws-p real-type)
   (apbmpc-order-laws-p real-type)
   (apbmpc-rational-laws-p real-type)))

(defun-sk algebra-apbmpcneq0-aeq0anbeq0anceq0-statement ()
  (forall (real-type a b c m n)
    (implies
     (and
      (apbmpc-real-structure-p real-type)
      (rationalp a)
      (rationalp b)
      (rationalp c)
      (apbmpc-real-p real-type m)
      (apbmpc-real-p real-type n)
      (apbmpc-lt real-type (apbmpc-zero real-type) m)
      (apbmpc-lt real-type (apbmpc-zero real-type) n)
      (equal
       (apbmpc-cube real-type m)
       (apbmpc-of-rational real-type 2))
      (equal
       (apbmpc-cube real-type n)
       (apbmpc-of-rational real-type 4))
      (equal
       (apbmpc-add
        real-type
        (apbmpc-of-rational real-type a)
        (apbmpc-add
         real-type
         (apbmpc-mul
          real-type
          (apbmpc-of-rational real-type b)
          m)
         (apbmpc-mul
          real-type
          (apbmpc-of-rational real-type c)
          n)))
       (apbmpc-zero real-type)))
     (and
      (equal a 0)
      (equal b 0)
      (equal c 0)))))

(value-triple :itpeval-statement-checked)
:q
