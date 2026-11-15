;; Statement-only formalization of miniF2F artifact amc12b_2002_p6:
        ;; nonzero real a and b whose two quadratic expressions agree for every real x must satisfy a=1 and b=-2.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub amcb02p6-real-p (value) t)
(defstub amcb02p6-zero () t)
(defstub amcb02p6-one () t)
(defstub amcb02p6-add (left right) t)
(defstub amcb02p6-mul (left right) t)
(defstub amcb02p6-neg (value) t)
(defstub amcb02p6-inv (value) t)
(defstub amcb02p6-lt (left right) t)
(defstub amcb02p6-of-rational (value) t)

(defun amcb02p6-sub (left right)
  (amcb02p6-add left (amcb02p6-neg right)))

(defun amcb02p6-div (left right)
  (amcb02p6-mul left (amcb02p6-inv right)))

(defun amcb02p6-le (left right)
  (or (equal left right) (amcb02p6-lt left right)))

(defun amcb02p6-nonnegative-p (value)
  (and (amcb02p6-real-p value)
       (amcb02p6-le (amcb02p6-zero) value)))

(defun amcb02p6-positive-p (value)
  (and (amcb02p6-real-p value)
       (amcb02p6-lt (amcb02p6-zero) value)))

(defun amcb02p6-abs (value)
  (if (amcb02p6-lt value (amcb02p6-zero))
      (amcb02p6-neg value)
    value))

(defun amcb02p6-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amcb02p6-one)
    (amcb02p6-mul
     value
     (amcb02p6-pow value (1- exponent)))))

(defun-sk amcb02p6-field-laws-p ()
  (forall (x y z)
    (and
     (amcb02p6-real-p (amcb02p6-zero))
     (amcb02p6-real-p (amcb02p6-one))
     (not (equal (amcb02p6-zero) (amcb02p6-one)))
     (implies
      (amcb02p6-real-p x)
      (and
       (amcb02p6-real-p (amcb02p6-neg x))
       (amcb02p6-real-p (amcb02p6-inv x))
       (equal (amcb02p6-add x (amcb02p6-zero)) x)
       (equal (amcb02p6-add x (amcb02p6-neg x))
              (amcb02p6-zero))
       (equal (amcb02p6-mul x (amcb02p6-one)) x)
       (implies
        (not (equal x (amcb02p6-zero)))
        (equal (amcb02p6-mul x (amcb02p6-inv x))
               (amcb02p6-one)))))
     (equal (amcb02p6-inv (amcb02p6-zero))
            (amcb02p6-zero))
     (implies
      (and (amcb02p6-real-p x)
           (amcb02p6-real-p y))
      (and
       (amcb02p6-real-p (amcb02p6-add x y))
       (amcb02p6-real-p (amcb02p6-mul x y))
       (equal (amcb02p6-add x y)
              (amcb02p6-add y x))
       (equal (amcb02p6-mul x y)
              (amcb02p6-mul y x))))
     (implies
      (and (amcb02p6-real-p x)
           (amcb02p6-real-p y)
           (amcb02p6-real-p z))
      (and
       (equal (amcb02p6-add (amcb02p6-add x y) z)
              (amcb02p6-add x (amcb02p6-add y z)))
       (equal (amcb02p6-mul (amcb02p6-mul x y) z)
              (amcb02p6-mul x (amcb02p6-mul y z)))
       (equal (amcb02p6-mul x (amcb02p6-add y z))
              (amcb02p6-add
               (amcb02p6-mul x y)
               (amcb02p6-mul x z))))))))

(defun-sk amcb02p6-order-laws-p ()
  (forall (x y z)
    (implies
     (and (amcb02p6-real-p x)
          (amcb02p6-real-p y)
          (amcb02p6-real-p z))
     (and
      (not (amcb02p6-lt x x))
      (or (equal x y)
          (amcb02p6-lt x y)
          (amcb02p6-lt y x))
      (implies
       (and (amcb02p6-lt x y)
            (amcb02p6-lt y z))
       (amcb02p6-lt x z))
      (implies
       (amcb02p6-lt x y)
       (amcb02p6-lt
        (amcb02p6-add x z)
        (amcb02p6-add y z)))
      (implies
       (and (amcb02p6-lt (amcb02p6-zero) x)
            (amcb02p6-lt (amcb02p6-zero) y))
       (amcb02p6-lt
        (amcb02p6-zero)
        (amcb02p6-mul x y)))))))

(defun-sk amcb02p6-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (amcb02p6-real-p (amcb02p6-of-rational a))
      (equal (amcb02p6-of-rational 0) (amcb02p6-zero))
      (equal (amcb02p6-of-rational 1) (amcb02p6-one))
      (equal
       (amcb02p6-of-rational (+ a b))
       (amcb02p6-add
        (amcb02p6-of-rational a)
        (amcb02p6-of-rational b)))
      (equal
       (amcb02p6-of-rational (* a b))
       (amcb02p6-mul
        (amcb02p6-of-rational a)
        (amcb02p6-of-rational b)))
      (equal
       (amcb02p6-of-rational (- a))
       (amcb02p6-neg (amcb02p6-of-rational a)))
      (iff
       (equal a b)
       (equal
        (amcb02p6-of-rational a)
        (amcb02p6-of-rational b)))
      (iff
       (< a b)
       (amcb02p6-lt
        (amcb02p6-of-rational a)
        (amcb02p6-of-rational b)))))))

(defun amcb02p6-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amcb02p6-real-p (car coefficients))
     (amcb02p6-polynomial-p (cdr coefficients)))))

(defun amcb02p6-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amcb02p6-zero)
    (amcb02p6-add
     (car coefficients)
     (amcb02p6-mul
      x
      (amcb02p6-polynomial-value
       (cdr coefficients) x)))))

(defun amcb02p6-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amcb02p6-leading-coefficient (cdr coefficients))))

(defun amcb02p6-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amcb02p6-leading-coefficient coefficients)
     (amcb02p6-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amcb02p6-square-root-exists-p (x)
  (exists (root)
    (and
     (amcb02p6-nonnegative-p root)
     (equal (amcb02p6-mul root root) x))))

(defun-sk amcb02p6-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (amcb02p6-nonnegative-p x)
     (amcb02p6-square-root-exists-p x))))

(defun-sk amcb02p6-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (amcb02p6-real-p root)
     (equal
      (amcb02p6-polynomial-value coefficients root)
      (amcb02p6-zero)))))

(defun-sk amcb02p6-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amcb02p6-polynomial-p coefficients)
      (amcb02p6-odd-degree-p coefficients))
     (amcb02p6-polynomial-root-exists-p coefficients))))

(defun amcb02p6-real-closed-field-p ()
  (and
   (amcb02p6-field-laws-p)
   (amcb02p6-order-laws-p)
   (amcb02p6-rational-laws-p)
   (amcb02p6-lt (amcb02p6-zero) (amcb02p6-one))
   (amcb02p6-nonnegative-square-roots-p)
   (amcb02p6-odd-polynomial-roots-p)))

(defun amcb02p6-principal-square-root-p (root value)
  (and
   (amcb02p6-nonnegative-p root)
   (equal (amcb02p6-mul root root) value)))

(defchoose amcb02p6-sqrt (root) (value)
  (amcb02p6-principal-square-root-p root value))

        (defun-sk amcb02p6-polynomial-law-p (a b)
  (forall (x)
    (implies
     (amcb02p6-real-p x)
     (equal
      (amcb02p6-add
       (amcb02p6-add
        (amcb02p6-pow x 2)
        (amcb02p6-mul a x))
       b)
      (amcb02p6-mul
       (amcb02p6-sub x a)
       (amcb02p6-sub x b))))))

(defun amc12b-2002-p6-statement (a b)
  (implies
   (and
    (amcb02p6-real-closed-field-p)
    (amcb02p6-real-p a)
    (amcb02p6-real-p b)
    (not (equal a (amcb02p6-zero)))
    (not (equal b (amcb02p6-zero)))
    (amcb02p6-polynomial-law-p a b))
   (and
    (equal a (amcb02p6-one))
    (equal b (amcb02p6-of-rational -2)))))

        (value-triple :itpeval-statement-checked)
        :q
