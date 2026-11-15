;; Statement-only formalization of miniF2F artifact imo_1965_p1:
        ;; the source inequalities, expressed by the unit-circle coordinates of x in [0,2*pi], imply the equivalent target arc condition.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub imo65p1-real-p (value) t)
(defstub imo65p1-zero () t)
(defstub imo65p1-one () t)
(defstub imo65p1-add (left right) t)
(defstub imo65p1-mul (left right) t)
(defstub imo65p1-neg (value) t)
(defstub imo65p1-inv (value) t)
(defstub imo65p1-lt (left right) t)
(defstub imo65p1-of-rational (value) t)

(defun imo65p1-sub (left right)
  (imo65p1-add left (imo65p1-neg right)))

(defun imo65p1-div (left right)
  (imo65p1-mul left (imo65p1-inv right)))

(defun imo65p1-le (left right)
  (or (equal left right) (imo65p1-lt left right)))

(defun imo65p1-nonnegative-p (value)
  (and (imo65p1-real-p value)
       (imo65p1-le (imo65p1-zero) value)))

(defun imo65p1-positive-p (value)
  (and (imo65p1-real-p value)
       (imo65p1-lt (imo65p1-zero) value)))

(defun imo65p1-abs (value)
  (if (imo65p1-lt value (imo65p1-zero))
      (imo65p1-neg value)
    value))

(defun imo65p1-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (imo65p1-one)
    (imo65p1-mul
     value
     (imo65p1-pow value (1- exponent)))))

(defun-sk imo65p1-field-laws-p ()
  (forall (x y z)
    (and
     (imo65p1-real-p (imo65p1-zero))
     (imo65p1-real-p (imo65p1-one))
     (not (equal (imo65p1-zero) (imo65p1-one)))
     (implies
      (imo65p1-real-p x)
      (and
       (imo65p1-real-p (imo65p1-neg x))
       (imo65p1-real-p (imo65p1-inv x))
       (equal (imo65p1-add x (imo65p1-zero)) x)
       (equal (imo65p1-add x (imo65p1-neg x))
              (imo65p1-zero))
       (equal (imo65p1-mul x (imo65p1-one)) x)
       (implies
        (not (equal x (imo65p1-zero)))
        (equal (imo65p1-mul x (imo65p1-inv x))
               (imo65p1-one)))))
     (equal (imo65p1-inv (imo65p1-zero))
            (imo65p1-zero))
     (implies
      (and (imo65p1-real-p x)
           (imo65p1-real-p y))
      (and
       (imo65p1-real-p (imo65p1-add x y))
       (imo65p1-real-p (imo65p1-mul x y))
       (equal (imo65p1-add x y)
              (imo65p1-add y x))
       (equal (imo65p1-mul x y)
              (imo65p1-mul y x))))
     (implies
      (and (imo65p1-real-p x)
           (imo65p1-real-p y)
           (imo65p1-real-p z))
      (and
       (equal (imo65p1-add (imo65p1-add x y) z)
              (imo65p1-add x (imo65p1-add y z)))
       (equal (imo65p1-mul (imo65p1-mul x y) z)
              (imo65p1-mul x (imo65p1-mul y z)))
       (equal (imo65p1-mul x (imo65p1-add y z))
              (imo65p1-add
               (imo65p1-mul x y)
               (imo65p1-mul x z))))))))

(defun-sk imo65p1-order-laws-p ()
  (forall (x y z)
    (implies
     (and (imo65p1-real-p x)
          (imo65p1-real-p y)
          (imo65p1-real-p z))
     (and
      (not (imo65p1-lt x x))
      (or (equal x y)
          (imo65p1-lt x y)
          (imo65p1-lt y x))
      (implies
       (and (imo65p1-lt x y)
            (imo65p1-lt y z))
       (imo65p1-lt x z))
      (implies
       (imo65p1-lt x y)
       (imo65p1-lt
        (imo65p1-add x z)
        (imo65p1-add y z)))
      (implies
       (and (imo65p1-lt (imo65p1-zero) x)
            (imo65p1-lt (imo65p1-zero) y))
       (imo65p1-lt
        (imo65p1-zero)
        (imo65p1-mul x y)))))))

(defun-sk imo65p1-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (imo65p1-real-p (imo65p1-of-rational a))
      (equal (imo65p1-of-rational 0) (imo65p1-zero))
      (equal (imo65p1-of-rational 1) (imo65p1-one))
      (equal
       (imo65p1-of-rational (+ a b))
       (imo65p1-add
        (imo65p1-of-rational a)
        (imo65p1-of-rational b)))
      (equal
       (imo65p1-of-rational (* a b))
       (imo65p1-mul
        (imo65p1-of-rational a)
        (imo65p1-of-rational b)))
      (equal
       (imo65p1-of-rational (- a))
       (imo65p1-neg (imo65p1-of-rational a)))
      (iff
       (equal a b)
       (equal
        (imo65p1-of-rational a)
        (imo65p1-of-rational b)))
      (iff
       (< a b)
       (imo65p1-lt
        (imo65p1-of-rational a)
        (imo65p1-of-rational b)))))))

(defun imo65p1-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (imo65p1-real-p (car coefficients))
     (imo65p1-polynomial-p (cdr coefficients)))))

(defun imo65p1-polynomial-value (coefficients x)
  (if (endp coefficients)
      (imo65p1-zero)
    (imo65p1-add
     (car coefficients)
     (imo65p1-mul
      x
      (imo65p1-polynomial-value
       (cdr coefficients) x)))))

(defun imo65p1-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (imo65p1-leading-coefficient (cdr coefficients))))

(defun imo65p1-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (imo65p1-leading-coefficient coefficients)
     (imo65p1-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk imo65p1-square-root-exists-p (x)
  (exists (root)
    (and
     (imo65p1-nonnegative-p root)
     (equal (imo65p1-mul root root) x))))

(defun-sk imo65p1-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (imo65p1-nonnegative-p x)
     (imo65p1-square-root-exists-p x))))

(defun-sk imo65p1-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (imo65p1-real-p root)
     (equal
      (imo65p1-polynomial-value coefficients root)
      (imo65p1-zero)))))

(defun-sk imo65p1-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (imo65p1-polynomial-p coefficients)
      (imo65p1-odd-degree-p coefficients))
     (imo65p1-polynomial-root-exists-p coefficients))))

(defun imo65p1-real-closed-field-p ()
  (and
   (imo65p1-field-laws-p)
   (imo65p1-order-laws-p)
   (imo65p1-rational-laws-p)
   (imo65p1-lt (imo65p1-zero) (imo65p1-one))
   (imo65p1-nonnegative-square-roots-p)
   (imo65p1-odd-polynomial-roots-p)))

(defun imo65p1-principal-square-root-p (root value)
  (and
   (imo65p1-nonnegative-p root)
   (equal (imo65p1-mul root root) value)))

(defchoose imo65p1-sqrt (root) (value)
  (imo65p1-principal-square-root-p root value))

        (defun imo-1965-p1-statement (cosine-x sine-x)
  (let* ((sine-two-x
          (imo65p1-mul
           (imo65p1-of-rational 2)
           (imo65p1-mul sine-x cosine-x)))
         (sqrt-one-plus-sine-two-x
          (imo65p1-sqrt
           (imo65p1-add
            (imo65p1-one)
            sine-two-x)))
         (sqrt-one-minus-sine-two-x
          (imo65p1-sqrt
           (imo65p1-sub
            (imo65p1-one)
            sine-two-x)))
         (radical-difference
          (imo65p1-abs
           (imo65p1-sub
            sqrt-one-plus-sine-two-x
            sqrt-one-minus-sine-two-x))))
    (implies
     (and
      (imo65p1-real-closed-field-p)
      (imo65p1-real-p cosine-x)
      (imo65p1-real-p sine-x)
      (equal
       (imo65p1-add
        (imo65p1-pow cosine-x 2)
        (imo65p1-pow sine-x 2))
       (imo65p1-one))
      (imo65p1-le
       (imo65p1-mul
        (imo65p1-of-rational 2)
        cosine-x)
       radical-difference)
      (imo65p1-le
       radical-difference
       (imo65p1-sqrt
        (imo65p1-of-rational 2))))
     (imo65p1-le
      cosine-x
      (imo65p1-abs sine-x)))))

        (value-triple :itpeval-statement-checked)
        :q
