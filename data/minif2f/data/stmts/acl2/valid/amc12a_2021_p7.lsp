;; Statement-only formalization of miniF2F artifact amc12a_2021_p7:
        ;; all real x and y satisfy 1 <= (xy-1)^2 + (x+y)^2.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub amca21p7-real-p (value) t)
(defstub amca21p7-zero () t)
(defstub amca21p7-one () t)
(defstub amca21p7-add (left right) t)
(defstub amca21p7-mul (left right) t)
(defstub amca21p7-neg (value) t)
(defstub amca21p7-inv (value) t)
(defstub amca21p7-lt (left right) t)
(defstub amca21p7-of-rational (value) t)

(defun amca21p7-sub (left right)
  (amca21p7-add left (amca21p7-neg right)))

(defun amca21p7-div (left right)
  (amca21p7-mul left (amca21p7-inv right)))

(defun amca21p7-le (left right)
  (or (equal left right) (amca21p7-lt left right)))

(defun amca21p7-nonnegative-p (value)
  (and (amca21p7-real-p value)
       (amca21p7-le (amca21p7-zero) value)))

(defun amca21p7-positive-p (value)
  (and (amca21p7-real-p value)
       (amca21p7-lt (amca21p7-zero) value)))

(defun amca21p7-abs (value)
  (if (amca21p7-lt value (amca21p7-zero))
      (amca21p7-neg value)
    value))

(defun amca21p7-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amca21p7-one)
    (amca21p7-mul
     value
     (amca21p7-pow value (1- exponent)))))

(defun-sk amca21p7-field-laws-p ()
  (forall (x y z)
    (and
     (amca21p7-real-p (amca21p7-zero))
     (amca21p7-real-p (amca21p7-one))
     (not (equal (amca21p7-zero) (amca21p7-one)))
     (implies
      (amca21p7-real-p x)
      (and
       (amca21p7-real-p (amca21p7-neg x))
       (amca21p7-real-p (amca21p7-inv x))
       (equal (amca21p7-add x (amca21p7-zero)) x)
       (equal (amca21p7-add x (amca21p7-neg x))
              (amca21p7-zero))
       (equal (amca21p7-mul x (amca21p7-one)) x)
       (implies
        (not (equal x (amca21p7-zero)))
        (equal (amca21p7-mul x (amca21p7-inv x))
               (amca21p7-one)))))
     (equal (amca21p7-inv (amca21p7-zero))
            (amca21p7-zero))
     (implies
      (and (amca21p7-real-p x)
           (amca21p7-real-p y))
      (and
       (amca21p7-real-p (amca21p7-add x y))
       (amca21p7-real-p (amca21p7-mul x y))
       (equal (amca21p7-add x y)
              (amca21p7-add y x))
       (equal (amca21p7-mul x y)
              (amca21p7-mul y x))))
     (implies
      (and (amca21p7-real-p x)
           (amca21p7-real-p y)
           (amca21p7-real-p z))
      (and
       (equal (amca21p7-add (amca21p7-add x y) z)
              (amca21p7-add x (amca21p7-add y z)))
       (equal (amca21p7-mul (amca21p7-mul x y) z)
              (amca21p7-mul x (amca21p7-mul y z)))
       (equal (amca21p7-mul x (amca21p7-add y z))
              (amca21p7-add
               (amca21p7-mul x y)
               (amca21p7-mul x z))))))))

(defun-sk amca21p7-order-laws-p ()
  (forall (x y z)
    (implies
     (and (amca21p7-real-p x)
          (amca21p7-real-p y)
          (amca21p7-real-p z))
     (and
      (not (amca21p7-lt x x))
      (or (equal x y)
          (amca21p7-lt x y)
          (amca21p7-lt y x))
      (implies
       (and (amca21p7-lt x y)
            (amca21p7-lt y z))
       (amca21p7-lt x z))
      (implies
       (amca21p7-lt x y)
       (amca21p7-lt
        (amca21p7-add x z)
        (amca21p7-add y z)))
      (implies
       (and (amca21p7-lt (amca21p7-zero) x)
            (amca21p7-lt (amca21p7-zero) y))
       (amca21p7-lt
        (amca21p7-zero)
        (amca21p7-mul x y)))))))

(defun-sk amca21p7-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (amca21p7-real-p (amca21p7-of-rational a))
      (equal (amca21p7-of-rational 0) (amca21p7-zero))
      (equal (amca21p7-of-rational 1) (amca21p7-one))
      (equal
       (amca21p7-of-rational (+ a b))
       (amca21p7-add
        (amca21p7-of-rational a)
        (amca21p7-of-rational b)))
      (equal
       (amca21p7-of-rational (* a b))
       (amca21p7-mul
        (amca21p7-of-rational a)
        (amca21p7-of-rational b)))
      (equal
       (amca21p7-of-rational (- a))
       (amca21p7-neg (amca21p7-of-rational a)))
      (iff
       (equal a b)
       (equal
        (amca21p7-of-rational a)
        (amca21p7-of-rational b)))
      (iff
       (< a b)
       (amca21p7-lt
        (amca21p7-of-rational a)
        (amca21p7-of-rational b)))))))

(defun amca21p7-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amca21p7-real-p (car coefficients))
     (amca21p7-polynomial-p (cdr coefficients)))))

(defun amca21p7-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amca21p7-zero)
    (amca21p7-add
     (car coefficients)
     (amca21p7-mul
      x
      (amca21p7-polynomial-value
       (cdr coefficients) x)))))

(defun amca21p7-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amca21p7-leading-coefficient (cdr coefficients))))

(defun amca21p7-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amca21p7-leading-coefficient coefficients)
     (amca21p7-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amca21p7-square-root-exists-p (x)
  (exists (root)
    (and
     (amca21p7-nonnegative-p root)
     (equal (amca21p7-mul root root) x))))

(defun-sk amca21p7-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (amca21p7-nonnegative-p x)
     (amca21p7-square-root-exists-p x))))

(defun-sk amca21p7-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (amca21p7-real-p root)
     (equal
      (amca21p7-polynomial-value coefficients root)
      (amca21p7-zero)))))

(defun-sk amca21p7-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amca21p7-polynomial-p coefficients)
      (amca21p7-odd-degree-p coefficients))
     (amca21p7-polynomial-root-exists-p coefficients))))

(defun amca21p7-real-closed-field-p ()
  (and
   (amca21p7-field-laws-p)
   (amca21p7-order-laws-p)
   (amca21p7-rational-laws-p)
   (amca21p7-lt (amca21p7-zero) (amca21p7-one))
   (amca21p7-nonnegative-square-roots-p)
   (amca21p7-odd-polynomial-roots-p)))

(defun amca21p7-principal-square-root-p (root value)
  (and
   (amca21p7-nonnegative-p root)
   (equal (amca21p7-mul root root) value)))

(defchoose amca21p7-sqrt (root) (value)
  (amca21p7-principal-square-root-p root value))

        (defun amc12a-2021-p7-statement (x y)
  (implies
   (and
    (amca21p7-real-closed-field-p)
    (amca21p7-real-p x)
    (amca21p7-real-p y))
   (amca21p7-le
    (amca21p7-one)
    (amca21p7-add
     (amca21p7-pow
      (amca21p7-sub
       (amca21p7-mul x y)
       (amca21p7-one))
      2)
     (amca21p7-pow
      (amca21p7-add x y)
      2)))))

        (value-triple :itpeval-statement-checked)
        :q
