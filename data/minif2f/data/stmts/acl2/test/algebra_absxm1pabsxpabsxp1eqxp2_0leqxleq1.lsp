;; Statement-only formalization of miniF2F artifact algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1:
        ;; |x - 1| + |x| + |x + 1| = x + 2 for a real x implies 0 <= x <= 1.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub abs3-real-p (value) t)
(defstub abs3-zero () t)
(defstub abs3-one () t)
(defstub abs3-add (left right) t)
(defstub abs3-mul (left right) t)
(defstub abs3-neg (value) t)
(defstub abs3-inv (value) t)
(defstub abs3-lt (left right) t)
(defstub abs3-of-rational (value) t)

(defun abs3-sub (left right)
  (abs3-add left (abs3-neg right)))

(defun abs3-div (left right)
  (abs3-mul left (abs3-inv right)))

(defun abs3-le (left right)
  (or (equal left right) (abs3-lt left right)))

(defun abs3-nonnegative-p (value)
  (and (abs3-real-p value)
       (abs3-le (abs3-zero) value)))

(defun abs3-positive-p (value)
  (and (abs3-real-p value)
       (abs3-lt (abs3-zero) value)))

(defun abs3-abs (value)
  (if (abs3-lt value (abs3-zero))
      (abs3-neg value)
    value))

(defun abs3-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (abs3-one)
    (abs3-mul
     value
     (abs3-pow value (1- exponent)))))

(defun-sk abs3-field-laws-p ()
  (forall (x y z)
    (and
     (abs3-real-p (abs3-zero))
     (abs3-real-p (abs3-one))
     (not (equal (abs3-zero) (abs3-one)))
     (implies
      (abs3-real-p x)
      (and
       (abs3-real-p (abs3-neg x))
       (abs3-real-p (abs3-inv x))
       (equal (abs3-add x (abs3-zero)) x)
       (equal (abs3-add x (abs3-neg x))
              (abs3-zero))
       (equal (abs3-mul x (abs3-one)) x)
       (implies
        (not (equal x (abs3-zero)))
        (equal (abs3-mul x (abs3-inv x))
               (abs3-one)))))
     (equal (abs3-inv (abs3-zero))
            (abs3-zero))
     (implies
      (and (abs3-real-p x)
           (abs3-real-p y))
      (and
       (abs3-real-p (abs3-add x y))
       (abs3-real-p (abs3-mul x y))
       (equal (abs3-add x y)
              (abs3-add y x))
       (equal (abs3-mul x y)
              (abs3-mul y x))))
     (implies
      (and (abs3-real-p x)
           (abs3-real-p y)
           (abs3-real-p z))
      (and
       (equal (abs3-add (abs3-add x y) z)
              (abs3-add x (abs3-add y z)))
       (equal (abs3-mul (abs3-mul x y) z)
              (abs3-mul x (abs3-mul y z)))
       (equal (abs3-mul x (abs3-add y z))
              (abs3-add
               (abs3-mul x y)
               (abs3-mul x z))))))))

(defun-sk abs3-order-laws-p ()
  (forall (x y z)
    (implies
     (and (abs3-real-p x)
          (abs3-real-p y)
          (abs3-real-p z))
     (and
      (not (abs3-lt x x))
      (or (equal x y)
          (abs3-lt x y)
          (abs3-lt y x))
      (implies
       (and (abs3-lt x y)
            (abs3-lt y z))
       (abs3-lt x z))
      (implies
       (abs3-lt x y)
       (abs3-lt
        (abs3-add x z)
        (abs3-add y z)))
      (implies
       (and (abs3-lt (abs3-zero) x)
            (abs3-lt (abs3-zero) y))
       (abs3-lt
        (abs3-zero)
        (abs3-mul x y)))))))

(defun-sk abs3-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (abs3-real-p (abs3-of-rational a))
      (equal (abs3-of-rational 0) (abs3-zero))
      (equal (abs3-of-rational 1) (abs3-one))
      (equal
       (abs3-of-rational (+ a b))
       (abs3-add
        (abs3-of-rational a)
        (abs3-of-rational b)))
      (equal
       (abs3-of-rational (* a b))
       (abs3-mul
        (abs3-of-rational a)
        (abs3-of-rational b)))
      (equal
       (abs3-of-rational (- a))
       (abs3-neg (abs3-of-rational a)))
      (iff
       (equal a b)
       (equal
        (abs3-of-rational a)
        (abs3-of-rational b)))
      (iff
       (< a b)
       (abs3-lt
        (abs3-of-rational a)
        (abs3-of-rational b)))))))

(defun abs3-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (abs3-real-p (car coefficients))
     (abs3-polynomial-p (cdr coefficients)))))

(defun abs3-polynomial-value (coefficients x)
  (if (endp coefficients)
      (abs3-zero)
    (abs3-add
     (car coefficients)
     (abs3-mul
      x
      (abs3-polynomial-value
       (cdr coefficients) x)))))

(defun abs3-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (abs3-leading-coefficient (cdr coefficients))))

(defun abs3-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (abs3-leading-coefficient coefficients)
     (abs3-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk abs3-square-root-exists-p (x)
  (exists (root)
    (and
     (abs3-nonnegative-p root)
     (equal (abs3-mul root root) x))))

(defun-sk abs3-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (abs3-nonnegative-p x)
     (abs3-square-root-exists-p x))))

(defun-sk abs3-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (abs3-real-p root)
     (equal
      (abs3-polynomial-value coefficients root)
      (abs3-zero)))))

(defun-sk abs3-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (abs3-polynomial-p coefficients)
      (abs3-odd-degree-p coefficients))
     (abs3-polynomial-root-exists-p coefficients))))

(defun abs3-real-closed-field-p ()
  (and
   (abs3-field-laws-p)
   (abs3-order-laws-p)
   (abs3-rational-laws-p)
   (abs3-lt (abs3-zero) (abs3-one))
   (abs3-nonnegative-square-roots-p)
   (abs3-odd-polynomial-roots-p)))

(defun abs3-principal-square-root-p (root value)
  (and
   (abs3-nonnegative-p root)
   (equal (abs3-mul root root) value)))

(defchoose abs3-sqrt (root) (value)
  (abs3-principal-square-root-p root value))

        (defun algebra-absxm1pabsxpabsxp1eqxp2-0leqxleq1-statement (x)
  (implies
   (and
    (abs3-real-closed-field-p)
    (abs3-real-p x)
    (equal
     (abs3-add
      (abs3-add
       (abs3-abs (abs3-sub x (abs3-of-rational 1)))
       (abs3-abs x))
      (abs3-abs (abs3-add x (abs3-of-rational 1))))
     (abs3-add x (abs3-of-rational 2))))
   (and
    (abs3-le (abs3-zero) x)
    (abs3-le x (abs3-of-rational 1)))))

        (value-triple :itpeval-statement-checked)
        :q
