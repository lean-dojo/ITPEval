;; Statement-only formalization of miniF2F artifact amc12b_2003_p17:
        ;; under the bijection u=ln(x), v=ln(y) for positive reals, the two source logarithmic equations imply ln(xy)=3/5.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub amcb03p17-real-p (value) t)
(defstub amcb03p17-zero () t)
(defstub amcb03p17-one () t)
(defstub amcb03p17-add (left right) t)
(defstub amcb03p17-mul (left right) t)
(defstub amcb03p17-neg (value) t)
(defstub amcb03p17-inv (value) t)
(defstub amcb03p17-lt (left right) t)
(defstub amcb03p17-of-rational (value) t)

(defun amcb03p17-sub (left right)
  (amcb03p17-add left (amcb03p17-neg right)))

(defun amcb03p17-div (left right)
  (amcb03p17-mul left (amcb03p17-inv right)))

(defun amcb03p17-le (left right)
  (or (equal left right) (amcb03p17-lt left right)))

(defun amcb03p17-nonnegative-p (value)
  (and (amcb03p17-real-p value)
       (amcb03p17-le (amcb03p17-zero) value)))

(defun amcb03p17-positive-p (value)
  (and (amcb03p17-real-p value)
       (amcb03p17-lt (amcb03p17-zero) value)))

(defun amcb03p17-abs (value)
  (if (amcb03p17-lt value (amcb03p17-zero))
      (amcb03p17-neg value)
    value))

(defun amcb03p17-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amcb03p17-one)
    (amcb03p17-mul
     value
     (amcb03p17-pow value (1- exponent)))))

(defun-sk amcb03p17-field-laws-p ()
  (forall (x y z)
    (and
     (amcb03p17-real-p (amcb03p17-zero))
     (amcb03p17-real-p (amcb03p17-one))
     (not (equal (amcb03p17-zero) (amcb03p17-one)))
     (implies
      (amcb03p17-real-p x)
      (and
       (amcb03p17-real-p (amcb03p17-neg x))
       (amcb03p17-real-p (amcb03p17-inv x))
       (equal (amcb03p17-add x (amcb03p17-zero)) x)
       (equal (amcb03p17-add x (amcb03p17-neg x))
              (amcb03p17-zero))
       (equal (amcb03p17-mul x (amcb03p17-one)) x)
       (implies
        (not (equal x (amcb03p17-zero)))
        (equal (amcb03p17-mul x (amcb03p17-inv x))
               (amcb03p17-one)))))
     (equal (amcb03p17-inv (amcb03p17-zero))
            (amcb03p17-zero))
     (implies
      (and (amcb03p17-real-p x)
           (amcb03p17-real-p y))
      (and
       (amcb03p17-real-p (amcb03p17-add x y))
       (amcb03p17-real-p (amcb03p17-mul x y))
       (equal (amcb03p17-add x y)
              (amcb03p17-add y x))
       (equal (amcb03p17-mul x y)
              (amcb03p17-mul y x))))
     (implies
      (and (amcb03p17-real-p x)
           (amcb03p17-real-p y)
           (amcb03p17-real-p z))
      (and
       (equal (amcb03p17-add (amcb03p17-add x y) z)
              (amcb03p17-add x (amcb03p17-add y z)))
       (equal (amcb03p17-mul (amcb03p17-mul x y) z)
              (amcb03p17-mul x (amcb03p17-mul y z)))
       (equal (amcb03p17-mul x (amcb03p17-add y z))
              (amcb03p17-add
               (amcb03p17-mul x y)
               (amcb03p17-mul x z))))))))

(defun-sk amcb03p17-order-laws-p ()
  (forall (x y z)
    (implies
     (and (amcb03p17-real-p x)
          (amcb03p17-real-p y)
          (amcb03p17-real-p z))
     (and
      (not (amcb03p17-lt x x))
      (or (equal x y)
          (amcb03p17-lt x y)
          (amcb03p17-lt y x))
      (implies
       (and (amcb03p17-lt x y)
            (amcb03p17-lt y z))
       (amcb03p17-lt x z))
      (implies
       (amcb03p17-lt x y)
       (amcb03p17-lt
        (amcb03p17-add x z)
        (amcb03p17-add y z)))
      (implies
       (and (amcb03p17-lt (amcb03p17-zero) x)
            (amcb03p17-lt (amcb03p17-zero) y))
       (amcb03p17-lt
        (amcb03p17-zero)
        (amcb03p17-mul x y)))))))

(defun-sk amcb03p17-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (amcb03p17-real-p (amcb03p17-of-rational a))
      (equal (amcb03p17-of-rational 0) (amcb03p17-zero))
      (equal (amcb03p17-of-rational 1) (amcb03p17-one))
      (equal
       (amcb03p17-of-rational (+ a b))
       (amcb03p17-add
        (amcb03p17-of-rational a)
        (amcb03p17-of-rational b)))
      (equal
       (amcb03p17-of-rational (* a b))
       (amcb03p17-mul
        (amcb03p17-of-rational a)
        (amcb03p17-of-rational b)))
      (equal
       (amcb03p17-of-rational (- a))
       (amcb03p17-neg (amcb03p17-of-rational a)))
      (iff
       (equal a b)
       (equal
        (amcb03p17-of-rational a)
        (amcb03p17-of-rational b)))
      (iff
       (< a b)
       (amcb03p17-lt
        (amcb03p17-of-rational a)
        (amcb03p17-of-rational b)))))))

(defun amcb03p17-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amcb03p17-real-p (car coefficients))
     (amcb03p17-polynomial-p (cdr coefficients)))))

(defun amcb03p17-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amcb03p17-zero)
    (amcb03p17-add
     (car coefficients)
     (amcb03p17-mul
      x
      (amcb03p17-polynomial-value
       (cdr coefficients) x)))))

(defun amcb03p17-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amcb03p17-leading-coefficient (cdr coefficients))))

(defun amcb03p17-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amcb03p17-leading-coefficient coefficients)
     (amcb03p17-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amcb03p17-square-root-exists-p (x)
  (exists (root)
    (and
     (amcb03p17-nonnegative-p root)
     (equal (amcb03p17-mul root root) x))))

(defun-sk amcb03p17-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (amcb03p17-nonnegative-p x)
     (amcb03p17-square-root-exists-p x))))

(defun-sk amcb03p17-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (amcb03p17-real-p root)
     (equal
      (amcb03p17-polynomial-value coefficients root)
      (amcb03p17-zero)))))

(defun-sk amcb03p17-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amcb03p17-polynomial-p coefficients)
      (amcb03p17-odd-degree-p coefficients))
     (amcb03p17-polynomial-root-exists-p coefficients))))

(defun amcb03p17-real-closed-field-p ()
  (and
   (amcb03p17-field-laws-p)
   (amcb03p17-order-laws-p)
   (amcb03p17-rational-laws-p)
   (amcb03p17-lt (amcb03p17-zero) (amcb03p17-one))
   (amcb03p17-nonnegative-square-roots-p)
   (amcb03p17-odd-polynomial-roots-p)))

(defun amcb03p17-principal-square-root-p (root value)
  (and
   (amcb03p17-nonnegative-p root)
   (equal (amcb03p17-mul root root) value)))

(defchoose amcb03p17-sqrt (root) (value)
  (amcb03p17-principal-square-root-p root value))

        (defun amc12b-2003-p17-statement (u v)
  (implies
   (and
    (amcb03p17-real-closed-field-p)
    (amcb03p17-real-p u)
    (amcb03p17-real-p v)
    (equal
     (amcb03p17-add
      u
      (amcb03p17-mul
       (amcb03p17-of-rational 3) v))
     (amcb03p17-of-rational 1))
    (equal
     (amcb03p17-add
      (amcb03p17-mul
       (amcb03p17-of-rational 2) u)
      v)
     (amcb03p17-of-rational 1)))
   (equal
    (amcb03p17-add u v)
    (amcb03p17-of-rational 3/5))))

        (value-triple :itpeval-statement-checked)
        :q
