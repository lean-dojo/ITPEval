;; Statement-only formalization of miniF2F artifact amc12a_2010_p22:
        ;; for every real x, the sum from integer k=1 through 119 of |k*x-1| is at least 49.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub amca10p22-real-p (value) t)
(defstub amca10p22-zero () t)
(defstub amca10p22-one () t)
(defstub amca10p22-add (left right) t)
(defstub amca10p22-mul (left right) t)
(defstub amca10p22-neg (value) t)
(defstub amca10p22-inv (value) t)
(defstub amca10p22-lt (left right) t)
(defstub amca10p22-of-rational (value) t)

(defun amca10p22-sub (left right)
  (amca10p22-add left (amca10p22-neg right)))

(defun amca10p22-div (left right)
  (amca10p22-mul left (amca10p22-inv right)))

(defun amca10p22-le (left right)
  (or (equal left right) (amca10p22-lt left right)))

(defun amca10p22-nonnegative-p (value)
  (and (amca10p22-real-p value)
       (amca10p22-le (amca10p22-zero) value)))

(defun amca10p22-positive-p (value)
  (and (amca10p22-real-p value)
       (amca10p22-lt (amca10p22-zero) value)))

(defun amca10p22-abs (value)
  (if (amca10p22-lt value (amca10p22-zero))
      (amca10p22-neg value)
    value))

(defun amca10p22-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amca10p22-one)
    (amca10p22-mul
     value
     (amca10p22-pow value (1- exponent)))))

(defun-sk amca10p22-field-laws-p ()
  (forall (x y z)
    (and
     (amca10p22-real-p (amca10p22-zero))
     (amca10p22-real-p (amca10p22-one))
     (not (equal (amca10p22-zero) (amca10p22-one)))
     (implies
      (amca10p22-real-p x)
      (and
       (amca10p22-real-p (amca10p22-neg x))
       (amca10p22-real-p (amca10p22-inv x))
       (equal (amca10p22-add x (amca10p22-zero)) x)
       (equal (amca10p22-add x (amca10p22-neg x))
              (amca10p22-zero))
       (equal (amca10p22-mul x (amca10p22-one)) x)
       (implies
        (not (equal x (amca10p22-zero)))
        (equal (amca10p22-mul x (amca10p22-inv x))
               (amca10p22-one)))))
     (equal (amca10p22-inv (amca10p22-zero))
            (amca10p22-zero))
     (implies
      (and (amca10p22-real-p x)
           (amca10p22-real-p y))
      (and
       (amca10p22-real-p (amca10p22-add x y))
       (amca10p22-real-p (amca10p22-mul x y))
       (equal (amca10p22-add x y)
              (amca10p22-add y x))
       (equal (amca10p22-mul x y)
              (amca10p22-mul y x))))
     (implies
      (and (amca10p22-real-p x)
           (amca10p22-real-p y)
           (amca10p22-real-p z))
      (and
       (equal (amca10p22-add (amca10p22-add x y) z)
              (amca10p22-add x (amca10p22-add y z)))
       (equal (amca10p22-mul (amca10p22-mul x y) z)
              (amca10p22-mul x (amca10p22-mul y z)))
       (equal (amca10p22-mul x (amca10p22-add y z))
              (amca10p22-add
               (amca10p22-mul x y)
               (amca10p22-mul x z))))))))

(defun-sk amca10p22-order-laws-p ()
  (forall (x y z)
    (implies
     (and (amca10p22-real-p x)
          (amca10p22-real-p y)
          (amca10p22-real-p z))
     (and
      (not (amca10p22-lt x x))
      (or (equal x y)
          (amca10p22-lt x y)
          (amca10p22-lt y x))
      (implies
       (and (amca10p22-lt x y)
            (amca10p22-lt y z))
       (amca10p22-lt x z))
      (implies
       (amca10p22-lt x y)
       (amca10p22-lt
        (amca10p22-add x z)
        (amca10p22-add y z)))
      (implies
       (and (amca10p22-lt (amca10p22-zero) x)
            (amca10p22-lt (amca10p22-zero) y))
       (amca10p22-lt
        (amca10p22-zero)
        (amca10p22-mul x y)))))))

(defun-sk amca10p22-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (amca10p22-real-p (amca10p22-of-rational a))
      (equal (amca10p22-of-rational 0) (amca10p22-zero))
      (equal (amca10p22-of-rational 1) (amca10p22-one))
      (equal
       (amca10p22-of-rational (+ a b))
       (amca10p22-add
        (amca10p22-of-rational a)
        (amca10p22-of-rational b)))
      (equal
       (amca10p22-of-rational (* a b))
       (amca10p22-mul
        (amca10p22-of-rational a)
        (amca10p22-of-rational b)))
      (equal
       (amca10p22-of-rational (- a))
       (amca10p22-neg (amca10p22-of-rational a)))
      (iff
       (equal a b)
       (equal
        (amca10p22-of-rational a)
        (amca10p22-of-rational b)))
      (iff
       (< a b)
       (amca10p22-lt
        (amca10p22-of-rational a)
        (amca10p22-of-rational b)))))))

(defun amca10p22-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amca10p22-real-p (car coefficients))
     (amca10p22-polynomial-p (cdr coefficients)))))

(defun amca10p22-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amca10p22-zero)
    (amca10p22-add
     (car coefficients)
     (amca10p22-mul
      x
      (amca10p22-polynomial-value
       (cdr coefficients) x)))))

(defun amca10p22-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amca10p22-leading-coefficient (cdr coefficients))))

(defun amca10p22-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amca10p22-leading-coefficient coefficients)
     (amca10p22-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amca10p22-square-root-exists-p (x)
  (exists (root)
    (and
     (amca10p22-nonnegative-p root)
     (equal (amca10p22-mul root root) x))))

(defun-sk amca10p22-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (amca10p22-nonnegative-p x)
     (amca10p22-square-root-exists-p x))))

(defun-sk amca10p22-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (amca10p22-real-p root)
     (equal
      (amca10p22-polynomial-value coefficients root)
      (amca10p22-zero)))))

(defun-sk amca10p22-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amca10p22-polynomial-p coefficients)
      (amca10p22-odd-degree-p coefficients))
     (amca10p22-polynomial-root-exists-p coefficients))))

(defun amca10p22-real-closed-field-p ()
  (and
   (amca10p22-field-laws-p)
   (amca10p22-order-laws-p)
   (amca10p22-rational-laws-p)
   (amca10p22-lt (amca10p22-zero) (amca10p22-one))
   (amca10p22-nonnegative-square-roots-p)
   (amca10p22-odd-polynomial-roots-p)))

(defun amca10p22-principal-square-root-p (root value)
  (and
   (amca10p22-nonnegative-p root)
   (equal (amca10p22-mul root root) value)))

(defchoose amca10p22-sqrt (root) (value)
  (amca10p22-principal-square-root-p root value))

        (defun amca10p22-sum-from (x k count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (amca10p22-zero)
    (amca10p22-add
     (amca10p22-abs
      (amca10p22-sub
       (amca10p22-mul
        (amca10p22-of-rational k) x)
       (amca10p22-one)))
     (amca10p22-sum-from x (1+ k) (1- count)))))

(defun amc12a-2010-p22-statement (x)
  (implies
   (and
    (amca10p22-real-closed-field-p)
    (amca10p22-real-p x))
   (amca10p22-le
    (amca10p22-of-rational 49)
    (amca10p22-sum-from x 1 119))))

        (value-triple :itpeval-statement-checked)
        :q
