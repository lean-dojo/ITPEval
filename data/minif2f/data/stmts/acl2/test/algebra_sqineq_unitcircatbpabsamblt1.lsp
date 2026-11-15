;; Statement-only formalization of miniF2F artifact algebra_sqineq_unitcircatbpabsamblt1:
        ;; real a and b on the unit circle satisfy a*b + |a-b| <= 1.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub ucineq-real-p (value) t)
(defstub ucineq-zero () t)
(defstub ucineq-one () t)
(defstub ucineq-add (left right) t)
(defstub ucineq-mul (left right) t)
(defstub ucineq-neg (value) t)
(defstub ucineq-inv (value) t)
(defstub ucineq-lt (left right) t)
(defstub ucineq-of-rational (value) t)

(defun ucineq-sub (left right)
  (ucineq-add left (ucineq-neg right)))

(defun ucineq-div (left right)
  (ucineq-mul left (ucineq-inv right)))

(defun ucineq-le (left right)
  (or (equal left right) (ucineq-lt left right)))

(defun ucineq-nonnegative-p (value)
  (and (ucineq-real-p value)
       (ucineq-le (ucineq-zero) value)))

(defun ucineq-positive-p (value)
  (and (ucineq-real-p value)
       (ucineq-lt (ucineq-zero) value)))

(defun ucineq-abs (value)
  (if (ucineq-lt value (ucineq-zero))
      (ucineq-neg value)
    value))

(defun ucineq-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (ucineq-one)
    (ucineq-mul
     value
     (ucineq-pow value (1- exponent)))))

(defun-sk ucineq-field-laws-p ()
  (forall (x y z)
    (and
     (ucineq-real-p (ucineq-zero))
     (ucineq-real-p (ucineq-one))
     (not (equal (ucineq-zero) (ucineq-one)))
     (implies
      (ucineq-real-p x)
      (and
       (ucineq-real-p (ucineq-neg x))
       (ucineq-real-p (ucineq-inv x))
       (equal (ucineq-add x (ucineq-zero)) x)
       (equal (ucineq-add x (ucineq-neg x))
              (ucineq-zero))
       (equal (ucineq-mul x (ucineq-one)) x)
       (implies
        (not (equal x (ucineq-zero)))
        (equal (ucineq-mul x (ucineq-inv x))
               (ucineq-one)))))
     (equal (ucineq-inv (ucineq-zero))
            (ucineq-zero))
     (implies
      (and (ucineq-real-p x)
           (ucineq-real-p y))
      (and
       (ucineq-real-p (ucineq-add x y))
       (ucineq-real-p (ucineq-mul x y))
       (equal (ucineq-add x y)
              (ucineq-add y x))
       (equal (ucineq-mul x y)
              (ucineq-mul y x))))
     (implies
      (and (ucineq-real-p x)
           (ucineq-real-p y)
           (ucineq-real-p z))
      (and
       (equal (ucineq-add (ucineq-add x y) z)
              (ucineq-add x (ucineq-add y z)))
       (equal (ucineq-mul (ucineq-mul x y) z)
              (ucineq-mul x (ucineq-mul y z)))
       (equal (ucineq-mul x (ucineq-add y z))
              (ucineq-add
               (ucineq-mul x y)
               (ucineq-mul x z))))))))

(defun-sk ucineq-order-laws-p ()
  (forall (x y z)
    (implies
     (and (ucineq-real-p x)
          (ucineq-real-p y)
          (ucineq-real-p z))
     (and
      (not (ucineq-lt x x))
      (or (equal x y)
          (ucineq-lt x y)
          (ucineq-lt y x))
      (implies
       (and (ucineq-lt x y)
            (ucineq-lt y z))
       (ucineq-lt x z))
      (implies
       (ucineq-lt x y)
       (ucineq-lt
        (ucineq-add x z)
        (ucineq-add y z)))
      (implies
       (and (ucineq-lt (ucineq-zero) x)
            (ucineq-lt (ucineq-zero) y))
       (ucineq-lt
        (ucineq-zero)
        (ucineq-mul x y)))))))

(defun-sk ucineq-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (ucineq-real-p (ucineq-of-rational a))
      (equal (ucineq-of-rational 0) (ucineq-zero))
      (equal (ucineq-of-rational 1) (ucineq-one))
      (equal
       (ucineq-of-rational (+ a b))
       (ucineq-add
        (ucineq-of-rational a)
        (ucineq-of-rational b)))
      (equal
       (ucineq-of-rational (* a b))
       (ucineq-mul
        (ucineq-of-rational a)
        (ucineq-of-rational b)))
      (equal
       (ucineq-of-rational (- a))
       (ucineq-neg (ucineq-of-rational a)))
      (iff
       (equal a b)
       (equal
        (ucineq-of-rational a)
        (ucineq-of-rational b)))
      (iff
       (< a b)
       (ucineq-lt
        (ucineq-of-rational a)
        (ucineq-of-rational b)))))))

(defun ucineq-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (ucineq-real-p (car coefficients))
     (ucineq-polynomial-p (cdr coefficients)))))

(defun ucineq-polynomial-value (coefficients x)
  (if (endp coefficients)
      (ucineq-zero)
    (ucineq-add
     (car coefficients)
     (ucineq-mul
      x
      (ucineq-polynomial-value
       (cdr coefficients) x)))))

(defun ucineq-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (ucineq-leading-coefficient (cdr coefficients))))

(defun ucineq-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (ucineq-leading-coefficient coefficients)
     (ucineq-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk ucineq-square-root-exists-p (x)
  (exists (root)
    (and
     (ucineq-nonnegative-p root)
     (equal (ucineq-mul root root) x))))

(defun-sk ucineq-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (ucineq-nonnegative-p x)
     (ucineq-square-root-exists-p x))))

(defun-sk ucineq-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (ucineq-real-p root)
     (equal
      (ucineq-polynomial-value coefficients root)
      (ucineq-zero)))))

(defun-sk ucineq-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (ucineq-polynomial-p coefficients)
      (ucineq-odd-degree-p coefficients))
     (ucineq-polynomial-root-exists-p coefficients))))

(defun ucineq-real-closed-field-p ()
  (and
   (ucineq-field-laws-p)
   (ucineq-order-laws-p)
   (ucineq-rational-laws-p)
   (ucineq-lt (ucineq-zero) (ucineq-one))
   (ucineq-nonnegative-square-roots-p)
   (ucineq-odd-polynomial-roots-p)))

(defun ucineq-principal-square-root-p (root value)
  (and
   (ucineq-nonnegative-p root)
   (equal (ucineq-mul root root) value)))

(defchoose ucineq-sqrt (root) (value)
  (ucineq-principal-square-root-p root value))

        (defun algebra-sqineq-unitcircatbpabsamblt1-statement (a b)
  (implies
   (and
    (ucineq-real-closed-field-p)
    (ucineq-real-p a)
    (ucineq-real-p b)
    (equal
     (ucineq-add
      (ucineq-pow a 2)
      (ucineq-pow b 2))
     (ucineq-one)))
   (ucineq-le
    (ucineq-add
     (ucineq-mul a b)
     (ucineq-abs (ucineq-sub a b)))
    (ucineq-one))))

        (value-triple :itpeval-statement-checked)
        :q
