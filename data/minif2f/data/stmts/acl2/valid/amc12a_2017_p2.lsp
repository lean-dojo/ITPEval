;; Statement-only formalization of miniF2F artifact amc12a_2017_p2:
;; for all nonzero real x and y satisfying x+y = 4*x*y, the sum of their
;; reciprocals is equal to 4. This file contains no proof.
;;
;; ACL2 has no native real field. The arbitrary real-closed ordered field
;; carrier below preserves the source variables and operations directly.
;; Every law is an explicit premise; DEFSTUB introduces no law, and no
;; premise encodes the conclusion.

(in-package "ACL2")

(set-inhibit-output-lst '(proof-tree prove observation))

(defstub amc2017p2-real-p (value) t)
(defstub amc2017p2-zero () t)
(defstub amc2017p2-one () t)
(defstub amc2017p2-add (left right) t)
(defstub amc2017p2-mul (left right) t)
(defstub amc2017p2-neg (value) t)
(defstub amc2017p2-inv (value) t)
(defstub amc2017p2-le (left right) t)
(defstub amc2017p2-of-rational (value) t)

(defun amc2017p2-div (left right)
  (amc2017p2-mul left (amc2017p2-inv right)))

(defun-sk amc2017p2-field-laws-p ()
  (forall
   (x y z)
   (and
    (implies
     (and (amc2017p2-real-p x)
          (amc2017p2-real-p y))
     (and
      (amc2017p2-real-p (amc2017p2-add x y))
      (amc2017p2-real-p (amc2017p2-mul x y))))
    (implies
     (amc2017p2-real-p x)
     (and
      (amc2017p2-real-p (amc2017p2-neg x))
      (amc2017p2-real-p (amc2017p2-inv x))))
    (implies
     (and
      (amc2017p2-real-p x)
      (amc2017p2-real-p y)
      (amc2017p2-real-p z))
     (equal
      (amc2017p2-add (amc2017p2-add x y) z)
      (amc2017p2-add x (amc2017p2-add y z))))
    (implies
     (and (amc2017p2-real-p x)
          (amc2017p2-real-p y))
     (equal (amc2017p2-add x y)
            (amc2017p2-add y x)))
    (implies
     (amc2017p2-real-p x)
     (and
      (equal (amc2017p2-add x (amc2017p2-zero)) x)
      (equal
       (amc2017p2-add x (amc2017p2-neg x))
       (amc2017p2-zero))))
    (implies
     (and
      (amc2017p2-real-p x)
      (amc2017p2-real-p y)
      (amc2017p2-real-p z))
     (equal
      (amc2017p2-mul (amc2017p2-mul x y) z)
      (amc2017p2-mul x (amc2017p2-mul y z))))
    (implies
     (and (amc2017p2-real-p x)
          (amc2017p2-real-p y))
     (equal (amc2017p2-mul x y)
            (amc2017p2-mul y x)))
    (implies
     (amc2017p2-real-p x)
     (equal (amc2017p2-mul x (amc2017p2-one)) x))
    (implies
     (and
      (amc2017p2-real-p x)
      (not (equal x (amc2017p2-zero))))
     (equal
      (amc2017p2-mul x (amc2017p2-inv x))
      (amc2017p2-one)))
    (equal (amc2017p2-inv (amc2017p2-zero))
           (amc2017p2-zero))
    (implies
     (and
      (amc2017p2-real-p x)
      (amc2017p2-real-p y)
      (amc2017p2-real-p z))
     (equal
      (amc2017p2-mul x (amc2017p2-add y z))
      (amc2017p2-add
       (amc2017p2-mul x y)
       (amc2017p2-mul x z)))))))

(defun-sk amc2017p2-rational-laws-p ()
  (forall
   (p q)
   (implies
    (and (rationalp p)
         (rationalp q))
    (and
     (amc2017p2-real-p (amc2017p2-of-rational p))
     (equal (amc2017p2-of-rational 0)
            (amc2017p2-zero))
     (equal (amc2017p2-of-rational 1)
            (amc2017p2-one))
     (equal
      (amc2017p2-of-rational (+ p q))
      (amc2017p2-add
       (amc2017p2-of-rational p)
       (amc2017p2-of-rational q)))
     (equal
      (amc2017p2-of-rational (* p q))
      (amc2017p2-mul
       (amc2017p2-of-rational p)
       (amc2017p2-of-rational q)))
     (iff
      (equal p q)
      (equal
       (amc2017p2-of-rational p)
       (amc2017p2-of-rational q)))))))

(defun-sk amc2017p2-order-laws-p ()
  (forall
   (x y z)
   (implies
    (and
     (amc2017p2-real-p x)
     (amc2017p2-real-p y)
     (amc2017p2-real-p z))
    (and
     (amc2017p2-le x x)
     (implies
      (and (amc2017p2-le x y)
           (amc2017p2-le y x))
      (equal x y))
     (implies
      (and (amc2017p2-le x y)
           (amc2017p2-le y z))
      (amc2017p2-le x z))
     (or (amc2017p2-le x y)
         (amc2017p2-le y x))
     (implies
      (amc2017p2-le x y)
      (amc2017p2-le
       (amc2017p2-add x z)
       (amc2017p2-add y z)))
     (implies
      (and
       (amc2017p2-le (amc2017p2-zero) x)
       (amc2017p2-le (amc2017p2-zero) y))
      (amc2017p2-le
       (amc2017p2-zero)
       (amc2017p2-mul x y)))))))

(defun amc2017p2-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amc2017p2-real-p (car coefficients))
     (amc2017p2-polynomial-p (cdr coefficients)))))

(defun amc2017p2-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amc2017p2-zero)
    (amc2017p2-add
     (car coefficients)
     (amc2017p2-mul
      x
      (amc2017p2-polynomial-value
       (cdr coefficients) x)))))

(defun amc2017p2-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amc2017p2-leading-coefficient (cdr coefficients))))

(defun amc2017p2-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amc2017p2-leading-coefficient coefficients)
     (amc2017p2-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amc2017p2-square-root-exists-p (x)
  (exists (root)
    (and
     (amc2017p2-real-p root)
     (amc2017p2-le (amc2017p2-zero) root)
     (equal (amc2017p2-mul root root) x))))

(defun-sk amc2017p2-positive-square-roots-p ()
  (forall
   (x)
   (implies
    (and
     (amc2017p2-real-p x)
     (amc2017p2-le (amc2017p2-zero) x))
    (amc2017p2-square-root-exists-p x))))

(defun-sk amc2017p2-polynomial-root-exists-p
    (coefficients)
  (exists (root)
    (and
     (amc2017p2-real-p root)
     (equal
      (amc2017p2-polynomial-value coefficients root)
      (amc2017p2-zero)))))

(defun-sk amc2017p2-odd-polynomial-roots-p ()
  (forall
   (coefficients)
   (implies
    (and
     (true-listp coefficients)
     (amc2017p2-polynomial-p coefficients)
     (amc2017p2-odd-degree-p coefficients))
    (amc2017p2-polynomial-root-exists-p coefficients))))

(defun amc2017p2-real-field-p ()
  (and
   (amc2017p2-real-p (amc2017p2-zero))
   (amc2017p2-real-p (amc2017p2-one))
   (not (equal (amc2017p2-zero)
               (amc2017p2-one)))
   (amc2017p2-field-laws-p)
   (amc2017p2-rational-laws-p)
   (amc2017p2-order-laws-p)
   (amc2017p2-le
    (amc2017p2-zero)
    (amc2017p2-one))
   (amc2017p2-positive-square-roots-p)
   (amc2017p2-odd-polynomial-roots-p)))

(defun-sk amc12a-2017-p2-statement-p ()
  (forall
   (x y)
   (implies
    (and
     (amc2017p2-real-field-p)
     (amc2017p2-real-p x)
     (amc2017p2-real-p y)
     (not (equal x (amc2017p2-zero)))
     (not (equal y (amc2017p2-zero)))
     (equal
      (amc2017p2-add x y)
      (amc2017p2-mul
       (amc2017p2-of-rational 4)
       (amc2017p2-mul x y))))
    (equal
     (amc2017p2-add
      (amc2017p2-div (amc2017p2-one) x)
      (amc2017p2-div (amc2017p2-one) y))
     (amc2017p2-of-rational 4)))))

(value-triple :itpeval-statement-checked)
:q
