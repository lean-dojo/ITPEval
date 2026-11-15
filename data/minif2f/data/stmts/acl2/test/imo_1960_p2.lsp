;; Statement-only formalization of miniF2F artifact imo_1960_p2:
        ;; the source radical-domain, nonzero-denominator, and strict inequality hypotheses imply -1/2 <= x < 45/8.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub imo60p2-real-p (value) t)
(defstub imo60p2-zero () t)
(defstub imo60p2-one () t)
(defstub imo60p2-add (left right) t)
(defstub imo60p2-mul (left right) t)
(defstub imo60p2-neg (value) t)
(defstub imo60p2-inv (value) t)
(defstub imo60p2-lt (left right) t)
(defstub imo60p2-of-rational (value) t)

(defun imo60p2-sub (left right)
  (imo60p2-add left (imo60p2-neg right)))

(defun imo60p2-div (left right)
  (imo60p2-mul left (imo60p2-inv right)))

(defun imo60p2-le (left right)
  (or (equal left right) (imo60p2-lt left right)))

(defun imo60p2-nonnegative-p (value)
  (and (imo60p2-real-p value)
       (imo60p2-le (imo60p2-zero) value)))

(defun imo60p2-positive-p (value)
  (and (imo60p2-real-p value)
       (imo60p2-lt (imo60p2-zero) value)))

(defun imo60p2-abs (value)
  (if (imo60p2-lt value (imo60p2-zero))
      (imo60p2-neg value)
    value))

(defun imo60p2-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (imo60p2-one)
    (imo60p2-mul
     value
     (imo60p2-pow value (1- exponent)))))

(defun-sk imo60p2-field-laws-p ()
  (forall (x y z)
    (and
     (imo60p2-real-p (imo60p2-zero))
     (imo60p2-real-p (imo60p2-one))
     (not (equal (imo60p2-zero) (imo60p2-one)))
     (implies
      (imo60p2-real-p x)
      (and
       (imo60p2-real-p (imo60p2-neg x))
       (imo60p2-real-p (imo60p2-inv x))
       (equal (imo60p2-add x (imo60p2-zero)) x)
       (equal (imo60p2-add x (imo60p2-neg x))
              (imo60p2-zero))
       (equal (imo60p2-mul x (imo60p2-one)) x)
       (implies
        (not (equal x (imo60p2-zero)))
        (equal (imo60p2-mul x (imo60p2-inv x))
               (imo60p2-one)))))
     (equal (imo60p2-inv (imo60p2-zero))
            (imo60p2-zero))
     (implies
      (and (imo60p2-real-p x)
           (imo60p2-real-p y))
      (and
       (imo60p2-real-p (imo60p2-add x y))
       (imo60p2-real-p (imo60p2-mul x y))
       (equal (imo60p2-add x y)
              (imo60p2-add y x))
       (equal (imo60p2-mul x y)
              (imo60p2-mul y x))))
     (implies
      (and (imo60p2-real-p x)
           (imo60p2-real-p y)
           (imo60p2-real-p z))
      (and
       (equal (imo60p2-add (imo60p2-add x y) z)
              (imo60p2-add x (imo60p2-add y z)))
       (equal (imo60p2-mul (imo60p2-mul x y) z)
              (imo60p2-mul x (imo60p2-mul y z)))
       (equal (imo60p2-mul x (imo60p2-add y z))
              (imo60p2-add
               (imo60p2-mul x y)
               (imo60p2-mul x z))))))))

(defun-sk imo60p2-order-laws-p ()
  (forall (x y z)
    (implies
     (and (imo60p2-real-p x)
          (imo60p2-real-p y)
          (imo60p2-real-p z))
     (and
      (not (imo60p2-lt x x))
      (or (equal x y)
          (imo60p2-lt x y)
          (imo60p2-lt y x))
      (implies
       (and (imo60p2-lt x y)
            (imo60p2-lt y z))
       (imo60p2-lt x z))
      (implies
       (imo60p2-lt x y)
       (imo60p2-lt
        (imo60p2-add x z)
        (imo60p2-add y z)))
      (implies
       (and (imo60p2-lt (imo60p2-zero) x)
            (imo60p2-lt (imo60p2-zero) y))
       (imo60p2-lt
        (imo60p2-zero)
        (imo60p2-mul x y)))))))

(defun-sk imo60p2-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (imo60p2-real-p (imo60p2-of-rational a))
      (equal (imo60p2-of-rational 0) (imo60p2-zero))
      (equal (imo60p2-of-rational 1) (imo60p2-one))
      (equal
       (imo60p2-of-rational (+ a b))
       (imo60p2-add
        (imo60p2-of-rational a)
        (imo60p2-of-rational b)))
      (equal
       (imo60p2-of-rational (* a b))
       (imo60p2-mul
        (imo60p2-of-rational a)
        (imo60p2-of-rational b)))
      (equal
       (imo60p2-of-rational (- a))
       (imo60p2-neg (imo60p2-of-rational a)))
      (iff
       (equal a b)
       (equal
        (imo60p2-of-rational a)
        (imo60p2-of-rational b)))
      (iff
       (< a b)
       (imo60p2-lt
        (imo60p2-of-rational a)
        (imo60p2-of-rational b)))))))

(defun imo60p2-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (imo60p2-real-p (car coefficients))
     (imo60p2-polynomial-p (cdr coefficients)))))

(defun imo60p2-polynomial-value (coefficients x)
  (if (endp coefficients)
      (imo60p2-zero)
    (imo60p2-add
     (car coefficients)
     (imo60p2-mul
      x
      (imo60p2-polynomial-value
       (cdr coefficients) x)))))

(defun imo60p2-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (imo60p2-leading-coefficient (cdr coefficients))))

(defun imo60p2-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (imo60p2-leading-coefficient coefficients)
     (imo60p2-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk imo60p2-square-root-exists-p (x)
  (exists (root)
    (and
     (imo60p2-nonnegative-p root)
     (equal (imo60p2-mul root root) x))))

(defun-sk imo60p2-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (imo60p2-nonnegative-p x)
     (imo60p2-square-root-exists-p x))))

(defun-sk imo60p2-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (imo60p2-real-p root)
     (equal
      (imo60p2-polynomial-value coefficients root)
      (imo60p2-zero)))))

(defun-sk imo60p2-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (imo60p2-polynomial-p coefficients)
      (imo60p2-odd-degree-p coefficients))
     (imo60p2-polynomial-root-exists-p coefficients))))

(defun imo60p2-real-closed-field-p ()
  (and
   (imo60p2-field-laws-p)
   (imo60p2-order-laws-p)
   (imo60p2-rational-laws-p)
   (imo60p2-lt (imo60p2-zero) (imo60p2-one))
   (imo60p2-nonnegative-square-roots-p)
   (imo60p2-odd-polynomial-roots-p)))

(defun imo60p2-principal-square-root-p (root value)
  (and
   (imo60p2-nonnegative-p root)
   (equal (imo60p2-mul root root) value)))

(defchoose imo60p2-sqrt (root) (value)
  (imo60p2-principal-square-root-p root value))

        (defun imo-1960-p2-statement (x)
  (let* ((radicand
          (imo60p2-add
           (imo60p2-one)
           (imo60p2-mul
            (imo60p2-of-rational 2) x)))
         (root (imo60p2-sqrt radicand))
         (difference
          (imo60p2-sub (imo60p2-one) root))
         (difference-square
          (imo60p2-pow difference 2)))
    (implies
     (and
      (imo60p2-real-closed-field-p)
      (imo60p2-real-p x)
      (imo60p2-nonnegative-p radicand)
      (not (equal difference-square (imo60p2-zero)))
      (imo60p2-lt
       (imo60p2-div
        (imo60p2-mul
         (imo60p2-of-rational 4)
         (imo60p2-pow x 2))
        difference-square)
       (imo60p2-add
        (imo60p2-mul
         (imo60p2-of-rational 2) x)
        (imo60p2-of-rational 9)))
      (not (equal x (imo60p2-zero))))
     (and
      (imo60p2-le (imo60p2-of-rational -1/2) x)
      (imo60p2-lt x (imo60p2-of-rational 45/8))))))

        (value-triple :itpeval-statement-checked)
        :q
