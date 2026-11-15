;; Statement-only formalization of miniF2F artifact amc12a_2010_p10:
;; every real arithmetic sequence with a(1)=p, a(2)=9,
;; a(3)=3*p-q, and a(4)=3*p+q has a(2010)=8041. This file contains no proof.
;;
;; ACL2 has no native real field or first-class function quantifier. The
;; arbitrary DEFSTUB sequence and real-closed ordered field carrier preserve
;; the source objects directly. Every recurrence, codomain, and scalar law is
;; an explicit premise; no finite table or solved form replaces the sequence.

(in-package "ACL2")

(set-inhibit-output-lst '(proof-tree prove observation))

(defstub amc2010p10-real-p (value) t)
(defstub amc2010p10-zero () t)
(defstub amc2010p10-one () t)
(defstub amc2010p10-add (left right) t)
(defstub amc2010p10-mul (left right) t)
(defstub amc2010p10-neg (value) t)
(defstub amc2010p10-inv (value) t)
(defstub amc2010p10-le (left right) t)
(defstub amc2010p10-of-integer (value) t)
(defstub amc2010p10-a (index) t)

(defun amc2010p10-sub (left right)
  (amc2010p10-add left (amc2010p10-neg right)))

(defun-sk amc2010p10-ring-laws-p ()
  (forall
   (x y z)
   (and
    (implies
     (and (amc2010p10-real-p x)
          (amc2010p10-real-p y))
     (and
      (amc2010p10-real-p (amc2010p10-add x y))
      (amc2010p10-real-p (amc2010p10-mul x y))))
    (implies
     (amc2010p10-real-p x)
     (and
      (amc2010p10-real-p (amc2010p10-neg x))
      (amc2010p10-real-p (amc2010p10-inv x))))
    (implies
     (and
      (amc2010p10-real-p x)
      (amc2010p10-real-p y)
      (amc2010p10-real-p z))
     (equal
      (amc2010p10-add (amc2010p10-add x y) z)
      (amc2010p10-add x (amc2010p10-add y z))))
    (implies
     (and (amc2010p10-real-p x)
          (amc2010p10-real-p y))
     (equal (amc2010p10-add x y)
            (amc2010p10-add y x)))
    (implies
     (amc2010p10-real-p x)
     (and
      (equal (amc2010p10-add x (amc2010p10-zero)) x)
      (equal
       (amc2010p10-add x (amc2010p10-neg x))
       (amc2010p10-zero))))
    (implies
     (and
      (amc2010p10-real-p x)
      (amc2010p10-real-p y)
      (amc2010p10-real-p z))
     (equal
      (amc2010p10-mul (amc2010p10-mul x y) z)
      (amc2010p10-mul x (amc2010p10-mul y z))))
    (implies
     (and (amc2010p10-real-p x)
          (amc2010p10-real-p y))
     (equal (amc2010p10-mul x y)
            (amc2010p10-mul y x)))
    (implies
     (amc2010p10-real-p x)
     (equal (amc2010p10-mul x (amc2010p10-one)) x))
    (implies
     (and
      (amc2010p10-real-p x)
      (amc2010p10-real-p y)
      (amc2010p10-real-p z))
     (equal
      (amc2010p10-mul x (amc2010p10-add y z))
      (amc2010p10-add
       (amc2010p10-mul x y)
       (amc2010p10-mul x z)))))))

(defun-sk amc2010p10-inverse-laws-p ()
  (forall
   (x)
   (implies
    (amc2010p10-real-p x)
    (and
     (equal
      (amc2010p10-inv (amc2010p10-zero))
      (amc2010p10-zero))
     (implies
      (not (equal x (amc2010p10-zero)))
      (equal
       (amc2010p10-mul x (amc2010p10-inv x))
       (amc2010p10-one)))))))

(defun-sk amc2010p10-integer-laws-p ()
  (forall
   (m n)
   (implies
    (and (integerp m)
         (integerp n))
    (and
     (amc2010p10-real-p (amc2010p10-of-integer m))
     (equal (amc2010p10-of-integer 0)
            (amc2010p10-zero))
     (equal (amc2010p10-of-integer 1)
            (amc2010p10-one))
     (equal
      (amc2010p10-of-integer (+ m n))
      (amc2010p10-add
       (amc2010p10-of-integer m)
       (amc2010p10-of-integer n)))
     (equal
      (amc2010p10-of-integer (* m n))
      (amc2010p10-mul
       (amc2010p10-of-integer m)
       (amc2010p10-of-integer n)))
     (iff
      (equal m n)
      (equal
      (amc2010p10-of-integer m)
       (amc2010p10-of-integer n)))))))

(defun-sk amc2010p10-order-laws-p ()
  (forall
   (x y z)
   (implies
    (and
     (amc2010p10-real-p x)
     (amc2010p10-real-p y)
     (amc2010p10-real-p z))
    (and
     (amc2010p10-le x x)
     (implies
      (and (amc2010p10-le x y)
           (amc2010p10-le y x))
      (equal x y))
     (implies
      (and (amc2010p10-le x y)
           (amc2010p10-le y z))
      (amc2010p10-le x z))
     (or (amc2010p10-le x y)
         (amc2010p10-le y x))
     (implies
      (amc2010p10-le x y)
      (amc2010p10-le
       (amc2010p10-add x z)
       (amc2010p10-add y z)))
     (implies
      (and
       (amc2010p10-le (amc2010p10-zero) x)
       (amc2010p10-le (amc2010p10-zero) y))
      (amc2010p10-le
       (amc2010p10-zero)
       (amc2010p10-mul x y)))))))

(defun amc2010p10-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amc2010p10-real-p (car coefficients))
     (amc2010p10-polynomial-p (cdr coefficients)))))

(defun amc2010p10-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amc2010p10-zero)
    (amc2010p10-add
     (car coefficients)
     (amc2010p10-mul
      x
      (amc2010p10-polynomial-value
       (cdr coefficients) x)))))

(defun amc2010p10-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amc2010p10-leading-coefficient (cdr coefficients))))

(defun amc2010p10-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amc2010p10-leading-coefficient coefficients)
     (amc2010p10-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amc2010p10-square-root-exists-p (x)
  (exists
   (root)
   (and
    (amc2010p10-real-p root)
    (amc2010p10-le (amc2010p10-zero) root)
    (equal (amc2010p10-mul root root) x))))

(defun-sk amc2010p10-positive-square-roots-p ()
  (forall
   (x)
   (implies
    (and
     (amc2010p10-real-p x)
     (amc2010p10-le (amc2010p10-zero) x))
    (amc2010p10-square-root-exists-p x))))

(defun-sk amc2010p10-polynomial-root-exists-p
    (coefficients)
  (exists
   (root)
   (and
    (amc2010p10-real-p root)
    (equal
     (amc2010p10-polynomial-value coefficients root)
     (amc2010p10-zero)))))

(defun-sk amc2010p10-odd-polynomial-roots-p ()
  (forall
   (coefficients)
   (implies
    (and
     (true-listp coefficients)
     (amc2010p10-polynomial-p coefficients)
     (amc2010p10-odd-degree-p coefficients))
    (amc2010p10-polynomial-root-exists-p coefficients))))

(defun amc2010p10-real-ring-p ()
  (and
   (amc2010p10-real-p (amc2010p10-zero))
   (amc2010p10-real-p (amc2010p10-one))
   (not (equal (amc2010p10-zero)
               (amc2010p10-one)))
   (amc2010p10-ring-laws-p)
   (amc2010p10-inverse-laws-p)
   (amc2010p10-integer-laws-p)
   (amc2010p10-order-laws-p)
   (amc2010p10-le
    (amc2010p10-zero)
    (amc2010p10-one))
   (amc2010p10-positive-square-roots-p)
   (amc2010p10-odd-polynomial-roots-p)))

(defun-sk amc2010p10-sequence-codomain-p ()
  (forall
   (n)
   (implies
    (natp n)
    (amc2010p10-real-p (amc2010p10-a n)))))

(defun-sk amc2010p10-arithmetic-sequence-p ()
  (forall
   (n)
   (implies
    (natp n)
    (equal
     (amc2010p10-sub
      (amc2010p10-a (+ n 2))
      (amc2010p10-a (+ n 1)))
     (amc2010p10-sub
      (amc2010p10-a (+ n 1))
      (amc2010p10-a n))))))

(defun-sk amc12a-2010-p10-statement-p ()
  (forall
   (p q)
   (implies
    (and
     (amc2010p10-real-ring-p)
     (amc2010p10-sequence-codomain-p)
     (amc2010p10-arithmetic-sequence-p)
     (amc2010p10-real-p p)
     (amc2010p10-real-p q)
     (equal (amc2010p10-a 1) p)
     (equal
      (amc2010p10-a 2)
      (amc2010p10-of-integer 9))
     (equal
      (amc2010p10-a 3)
      (amc2010p10-sub
       (amc2010p10-mul
        (amc2010p10-of-integer 3)
        p)
       q))
     (equal
      (amc2010p10-a 4)
      (amc2010p10-add
       (amc2010p10-mul
        (amc2010p10-of-integer 3)
        p)
       q)))
    (equal
     (amc2010p10-a 2010)
     (amc2010p10-of-integer 8041)))))

(value-triple :itpeval-statement-checked)
:q
