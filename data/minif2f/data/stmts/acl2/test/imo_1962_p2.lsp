;; Statement-only formalization of miniF2F artifact imo_1962_p2:
        ;; the stated square-root inequality and radicand hypotheses imply -1 <= x < 1 - sqrt(31)/8.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub imo62p2-real-p (value) t)
(defstub imo62p2-zero () t)
(defstub imo62p2-one () t)
(defstub imo62p2-add (left right) t)
(defstub imo62p2-mul (left right) t)
(defstub imo62p2-neg (value) t)
(defstub imo62p2-inv (value) t)
(defstub imo62p2-lt (left right) t)
(defstub imo62p2-of-rational (value) t)

(defun imo62p2-sub (left right)
  (imo62p2-add left (imo62p2-neg right)))

(defun imo62p2-div (left right)
  (imo62p2-mul left (imo62p2-inv right)))

(defun imo62p2-le (left right)
  (or (equal left right) (imo62p2-lt left right)))

(defun imo62p2-nonnegative-p (value)
  (and (imo62p2-real-p value)
       (imo62p2-le (imo62p2-zero) value)))

(defun imo62p2-positive-p (value)
  (and (imo62p2-real-p value)
       (imo62p2-lt (imo62p2-zero) value)))

(defun imo62p2-abs (value)
  (if (imo62p2-lt value (imo62p2-zero))
      (imo62p2-neg value)
    value))

(defun imo62p2-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (imo62p2-one)
    (imo62p2-mul
     value
     (imo62p2-pow value (1- exponent)))))

(defun-sk imo62p2-field-laws-p ()
  (forall (x y z)
    (and
     (imo62p2-real-p (imo62p2-zero))
     (imo62p2-real-p (imo62p2-one))
     (not (equal (imo62p2-zero) (imo62p2-one)))
     (implies
      (imo62p2-real-p x)
      (and
       (imo62p2-real-p (imo62p2-neg x))
       (imo62p2-real-p (imo62p2-inv x))
       (equal (imo62p2-add x (imo62p2-zero)) x)
       (equal (imo62p2-add x (imo62p2-neg x))
              (imo62p2-zero))
       (equal (imo62p2-mul x (imo62p2-one)) x)
       (implies
        (not (equal x (imo62p2-zero)))
        (equal (imo62p2-mul x (imo62p2-inv x))
               (imo62p2-one)))))
     (equal (imo62p2-inv (imo62p2-zero))
            (imo62p2-zero))
     (implies
      (and (imo62p2-real-p x)
           (imo62p2-real-p y))
      (and
       (imo62p2-real-p (imo62p2-add x y))
       (imo62p2-real-p (imo62p2-mul x y))
       (equal (imo62p2-add x y)
              (imo62p2-add y x))
       (equal (imo62p2-mul x y)
              (imo62p2-mul y x))))
     (implies
      (and (imo62p2-real-p x)
           (imo62p2-real-p y)
           (imo62p2-real-p z))
      (and
       (equal (imo62p2-add (imo62p2-add x y) z)
              (imo62p2-add x (imo62p2-add y z)))
       (equal (imo62p2-mul (imo62p2-mul x y) z)
              (imo62p2-mul x (imo62p2-mul y z)))
       (equal (imo62p2-mul x (imo62p2-add y z))
              (imo62p2-add
               (imo62p2-mul x y)
               (imo62p2-mul x z))))))))

(defun-sk imo62p2-order-laws-p ()
  (forall (x y z)
    (implies
     (and (imo62p2-real-p x)
          (imo62p2-real-p y)
          (imo62p2-real-p z))
     (and
      (not (imo62p2-lt x x))
      (or (equal x y)
          (imo62p2-lt x y)
          (imo62p2-lt y x))
      (implies
       (and (imo62p2-lt x y)
            (imo62p2-lt y z))
       (imo62p2-lt x z))
      (implies
       (imo62p2-lt x y)
       (imo62p2-lt
        (imo62p2-add x z)
        (imo62p2-add y z)))
      (implies
       (and (imo62p2-lt (imo62p2-zero) x)
            (imo62p2-lt (imo62p2-zero) y))
       (imo62p2-lt
        (imo62p2-zero)
        (imo62p2-mul x y)))))))

(defun-sk imo62p2-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (imo62p2-real-p (imo62p2-of-rational a))
      (equal (imo62p2-of-rational 0) (imo62p2-zero))
      (equal (imo62p2-of-rational 1) (imo62p2-one))
      (equal
       (imo62p2-of-rational (+ a b))
       (imo62p2-add
        (imo62p2-of-rational a)
        (imo62p2-of-rational b)))
      (equal
       (imo62p2-of-rational (* a b))
       (imo62p2-mul
        (imo62p2-of-rational a)
        (imo62p2-of-rational b)))
      (equal
       (imo62p2-of-rational (- a))
       (imo62p2-neg (imo62p2-of-rational a)))
      (iff
       (equal a b)
       (equal
        (imo62p2-of-rational a)
        (imo62p2-of-rational b)))
      (iff
       (< a b)
       (imo62p2-lt
        (imo62p2-of-rational a)
        (imo62p2-of-rational b)))))))

(defun imo62p2-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (imo62p2-real-p (car coefficients))
     (imo62p2-polynomial-p (cdr coefficients)))))

(defun imo62p2-polynomial-value (coefficients x)
  (if (endp coefficients)
      (imo62p2-zero)
    (imo62p2-add
     (car coefficients)
     (imo62p2-mul
      x
      (imo62p2-polynomial-value
       (cdr coefficients) x)))))

(defun imo62p2-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (imo62p2-leading-coefficient (cdr coefficients))))

(defun imo62p2-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (imo62p2-leading-coefficient coefficients)
     (imo62p2-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk imo62p2-square-root-exists-p (x)
  (exists (root)
    (and
     (imo62p2-nonnegative-p root)
     (equal (imo62p2-mul root root) x))))

(defun-sk imo62p2-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (imo62p2-nonnegative-p x)
     (imo62p2-square-root-exists-p x))))

(defun-sk imo62p2-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (imo62p2-real-p root)
     (equal
      (imo62p2-polynomial-value coefficients root)
      (imo62p2-zero)))))

(defun-sk imo62p2-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (imo62p2-polynomial-p coefficients)
      (imo62p2-odd-degree-p coefficients))
     (imo62p2-polynomial-root-exists-p coefficients))))

(defun imo62p2-real-closed-field-p ()
  (and
   (imo62p2-field-laws-p)
   (imo62p2-order-laws-p)
   (imo62p2-rational-laws-p)
   (imo62p2-lt (imo62p2-zero) (imo62p2-one))
   (imo62p2-nonnegative-square-roots-p)
   (imo62p2-odd-polynomial-roots-p)))

(defun imo62p2-principal-square-root-p (root value)
  (and
   (imo62p2-nonnegative-p root)
   (equal (imo62p2-mul root root) value)))

(defchoose imo62p2-sqrt (root) (value)
  (imo62p2-principal-square-root-p root value))

        (defun imo-1962-p2-statement (x)
  (let ((left-radicand
         (imo62p2-sub (imo62p2-of-rational 3) x))
        (right-radicand
         (imo62p2-add x (imo62p2-one))))
    (implies
     (and
      (imo62p2-real-closed-field-p)
      (imo62p2-real-p x)
      (imo62p2-nonnegative-p left-radicand)
      (imo62p2-nonnegative-p right-radicand)
      (imo62p2-lt
       (imo62p2-of-rational 1/2)
       (imo62p2-sub
        (imo62p2-sqrt left-radicand)
        (imo62p2-sqrt right-radicand))))
     (and
      (imo62p2-le (imo62p2-of-rational -1) x)
      (imo62p2-lt
       x
       (imo62p2-sub
        (imo62p2-one)
        (imo62p2-div
         (imo62p2-sqrt
          (imo62p2-of-rational 31))
         (imo62p2-of-rational 8))))))))

        (value-triple :itpeval-statement-checked)
        :q
