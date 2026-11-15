;; Statement-only formalization of miniF2F artifact imo_1965_p2:
        ;; the nine real coefficients with the source sign, row-sum, and homogeneous linear-equation hypotheses force x=y=z=0.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub imo65p2-real-p (value) t)
(defstub imo65p2-zero () t)
(defstub imo65p2-one () t)
(defstub imo65p2-add (left right) t)
(defstub imo65p2-mul (left right) t)
(defstub imo65p2-neg (value) t)
(defstub imo65p2-inv (value) t)
(defstub imo65p2-lt (left right) t)
(defstub imo65p2-of-rational (value) t)

(defun imo65p2-sub (left right)
  (imo65p2-add left (imo65p2-neg right)))

(defun imo65p2-div (left right)
  (imo65p2-mul left (imo65p2-inv right)))

(defun imo65p2-le (left right)
  (or (equal left right) (imo65p2-lt left right)))

(defun imo65p2-nonnegative-p (value)
  (and (imo65p2-real-p value)
       (imo65p2-le (imo65p2-zero) value)))

(defun imo65p2-positive-p (value)
  (and (imo65p2-real-p value)
       (imo65p2-lt (imo65p2-zero) value)))

(defun imo65p2-abs (value)
  (if (imo65p2-lt value (imo65p2-zero))
      (imo65p2-neg value)
    value))

(defun imo65p2-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (imo65p2-one)
    (imo65p2-mul
     value
     (imo65p2-pow value (1- exponent)))))

(defun-sk imo65p2-field-laws-p ()
  (forall (x y z)
    (and
     (imo65p2-real-p (imo65p2-zero))
     (imo65p2-real-p (imo65p2-one))
     (not (equal (imo65p2-zero) (imo65p2-one)))
     (implies
      (imo65p2-real-p x)
      (and
       (imo65p2-real-p (imo65p2-neg x))
       (imo65p2-real-p (imo65p2-inv x))
       (equal (imo65p2-add x (imo65p2-zero)) x)
       (equal (imo65p2-add x (imo65p2-neg x))
              (imo65p2-zero))
       (equal (imo65p2-mul x (imo65p2-one)) x)
       (implies
        (not (equal x (imo65p2-zero)))
        (equal (imo65p2-mul x (imo65p2-inv x))
               (imo65p2-one)))))
     (equal (imo65p2-inv (imo65p2-zero))
            (imo65p2-zero))
     (implies
      (and (imo65p2-real-p x)
           (imo65p2-real-p y))
      (and
       (imo65p2-real-p (imo65p2-add x y))
       (imo65p2-real-p (imo65p2-mul x y))
       (equal (imo65p2-add x y)
              (imo65p2-add y x))
       (equal (imo65p2-mul x y)
              (imo65p2-mul y x))))
     (implies
      (and (imo65p2-real-p x)
           (imo65p2-real-p y)
           (imo65p2-real-p z))
      (and
       (equal (imo65p2-add (imo65p2-add x y) z)
              (imo65p2-add x (imo65p2-add y z)))
       (equal (imo65p2-mul (imo65p2-mul x y) z)
              (imo65p2-mul x (imo65p2-mul y z)))
       (equal (imo65p2-mul x (imo65p2-add y z))
              (imo65p2-add
               (imo65p2-mul x y)
               (imo65p2-mul x z))))))))

(defun-sk imo65p2-order-laws-p ()
  (forall (x y z)
    (implies
     (and (imo65p2-real-p x)
          (imo65p2-real-p y)
          (imo65p2-real-p z))
     (and
      (not (imo65p2-lt x x))
      (or (equal x y)
          (imo65p2-lt x y)
          (imo65p2-lt y x))
      (implies
       (and (imo65p2-lt x y)
            (imo65p2-lt y z))
       (imo65p2-lt x z))
      (implies
       (imo65p2-lt x y)
       (imo65p2-lt
        (imo65p2-add x z)
        (imo65p2-add y z)))
      (implies
       (and (imo65p2-lt (imo65p2-zero) x)
            (imo65p2-lt (imo65p2-zero) y))
       (imo65p2-lt
        (imo65p2-zero)
        (imo65p2-mul x y)))))))

(defun-sk imo65p2-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (imo65p2-real-p (imo65p2-of-rational a))
      (equal (imo65p2-of-rational 0) (imo65p2-zero))
      (equal (imo65p2-of-rational 1) (imo65p2-one))
      (equal
       (imo65p2-of-rational (+ a b))
       (imo65p2-add
        (imo65p2-of-rational a)
        (imo65p2-of-rational b)))
      (equal
       (imo65p2-of-rational (* a b))
       (imo65p2-mul
        (imo65p2-of-rational a)
        (imo65p2-of-rational b)))
      (equal
       (imo65p2-of-rational (- a))
       (imo65p2-neg (imo65p2-of-rational a)))
      (iff
       (equal a b)
       (equal
        (imo65p2-of-rational a)
        (imo65p2-of-rational b)))
      (iff
       (< a b)
       (imo65p2-lt
        (imo65p2-of-rational a)
        (imo65p2-of-rational b)))))))

(defun imo65p2-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (imo65p2-real-p (car coefficients))
     (imo65p2-polynomial-p (cdr coefficients)))))

(defun imo65p2-polynomial-value (coefficients x)
  (if (endp coefficients)
      (imo65p2-zero)
    (imo65p2-add
     (car coefficients)
     (imo65p2-mul
      x
      (imo65p2-polynomial-value
       (cdr coefficients) x)))))

(defun imo65p2-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (imo65p2-leading-coefficient (cdr coefficients))))

(defun imo65p2-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (imo65p2-leading-coefficient coefficients)
     (imo65p2-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk imo65p2-square-root-exists-p (x)
  (exists (root)
    (and
     (imo65p2-nonnegative-p root)
     (equal (imo65p2-mul root root) x))))

(defun-sk imo65p2-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (imo65p2-nonnegative-p x)
     (imo65p2-square-root-exists-p x))))

(defun-sk imo65p2-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (imo65p2-real-p root)
     (equal
      (imo65p2-polynomial-value coefficients root)
      (imo65p2-zero)))))

(defun-sk imo65p2-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (imo65p2-polynomial-p coefficients)
      (imo65p2-odd-degree-p coefficients))
     (imo65p2-polynomial-root-exists-p coefficients))))

(defun imo65p2-real-closed-field-p ()
  (and
   (imo65p2-field-laws-p)
   (imo65p2-order-laws-p)
   (imo65p2-rational-laws-p)
   (imo65p2-lt (imo65p2-zero) (imo65p2-one))
   (imo65p2-nonnegative-square-roots-p)
   (imo65p2-odd-polynomial-roots-p)))

(defun imo65p2-principal-square-root-p (root value)
  (and
   (imo65p2-nonnegative-p root)
   (equal (imo65p2-mul root root) value)))

(defchoose imo65p2-sqrt (root) (value)
  (imo65p2-principal-square-root-p root value))

        (defun imo-1965-p2-statement
    (x y z a0 a1 a2 a3 a4 a5 a6 a7 a8)
  (implies
   (and
    (imo65p2-real-closed-field-p)
    (imo65p2-real-p x)
    (imo65p2-real-p y)
    (imo65p2-real-p z)
    (imo65p2-real-p a0)
    (imo65p2-real-p a1)
    (imo65p2-real-p a2)
    (imo65p2-real-p a3)
    (imo65p2-real-p a4)
    (imo65p2-real-p a5)
    (imo65p2-real-p a6)
    (imo65p2-real-p a7)
    (imo65p2-real-p a8)
    (imo65p2-lt (imo65p2-zero) a0)
    (imo65p2-lt (imo65p2-zero) a4)
    (imo65p2-lt (imo65p2-zero) a8)
    (imo65p2-lt a1 (imo65p2-zero))
    (imo65p2-lt a2 (imo65p2-zero))
    (imo65p2-lt a3 (imo65p2-zero))
    (imo65p2-lt a5 (imo65p2-zero))
    (imo65p2-lt a6 (imo65p2-zero))
    (imo65p2-lt a7 (imo65p2-zero))
    (imo65p2-lt
     (imo65p2-zero)
     (imo65p2-add (imo65p2-add a0 a1) a2))
    (imo65p2-lt
     (imo65p2-zero)
     (imo65p2-add (imo65p2-add a3 a4) a5))
    (imo65p2-lt
     (imo65p2-zero)
     (imo65p2-add (imo65p2-add a6 a7) a8))
    (equal
     (imo65p2-add
      (imo65p2-add
       (imo65p2-mul a0 x)
       (imo65p2-mul a1 y))
      (imo65p2-mul a2 z))
     (imo65p2-zero))
    (equal
     (imo65p2-add
      (imo65p2-add
       (imo65p2-mul a3 x)
       (imo65p2-mul a4 y))
      (imo65p2-mul a5 z))
     (imo65p2-zero))
    (equal
     (imo65p2-add
      (imo65p2-add
       (imo65p2-mul a6 x)
       (imo65p2-mul a7 y))
      (imo65p2-mul a8 z))
     (imo65p2-zero)))
   (and
    (equal x (imo65p2-zero))
    (equal y (imo65p2-zero))
    (equal z (imo65p2-zero)))))

        (value-triple :itpeval-statement-checked)
        :q
