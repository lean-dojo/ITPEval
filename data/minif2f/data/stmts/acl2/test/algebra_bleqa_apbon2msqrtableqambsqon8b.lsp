;; Statement-only formalization of miniF2F artifact algebra_bleqa_apbon2msqrtableqambsqon8b:
        ;; positive real a and b with b<=a satisfy the stated bound on the difference between their arithmetic and geometric means.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub agmerr-real-p (value) t)
(defstub agmerr-zero () t)
(defstub agmerr-one () t)
(defstub agmerr-add (left right) t)
(defstub agmerr-mul (left right) t)
(defstub agmerr-neg (value) t)
(defstub agmerr-inv (value) t)
(defstub agmerr-lt (left right) t)
(defstub agmerr-of-rational (value) t)

(defun agmerr-sub (left right)
  (agmerr-add left (agmerr-neg right)))

(defun agmerr-div (left right)
  (agmerr-mul left (agmerr-inv right)))

(defun agmerr-le (left right)
  (or (equal left right) (agmerr-lt left right)))

(defun agmerr-nonnegative-p (value)
  (and (agmerr-real-p value)
       (agmerr-le (agmerr-zero) value)))

(defun agmerr-positive-p (value)
  (and (agmerr-real-p value)
       (agmerr-lt (agmerr-zero) value)))

(defun agmerr-abs (value)
  (if (agmerr-lt value (agmerr-zero))
      (agmerr-neg value)
    value))

(defun agmerr-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (agmerr-one)
    (agmerr-mul
     value
     (agmerr-pow value (1- exponent)))))

(defun-sk agmerr-field-laws-p ()
  (forall (x y z)
    (and
     (agmerr-real-p (agmerr-zero))
     (agmerr-real-p (agmerr-one))
     (not (equal (agmerr-zero) (agmerr-one)))
     (implies
      (agmerr-real-p x)
      (and
       (agmerr-real-p (agmerr-neg x))
       (agmerr-real-p (agmerr-inv x))
       (equal (agmerr-add x (agmerr-zero)) x)
       (equal (agmerr-add x (agmerr-neg x))
              (agmerr-zero))
       (equal (agmerr-mul x (agmerr-one)) x)
       (implies
        (not (equal x (agmerr-zero)))
        (equal (agmerr-mul x (agmerr-inv x))
               (agmerr-one)))))
     (equal (agmerr-inv (agmerr-zero))
            (agmerr-zero))
     (implies
      (and (agmerr-real-p x)
           (agmerr-real-p y))
      (and
       (agmerr-real-p (agmerr-add x y))
       (agmerr-real-p (agmerr-mul x y))
       (equal (agmerr-add x y)
              (agmerr-add y x))
       (equal (agmerr-mul x y)
              (agmerr-mul y x))))
     (implies
      (and (agmerr-real-p x)
           (agmerr-real-p y)
           (agmerr-real-p z))
      (and
       (equal (agmerr-add (agmerr-add x y) z)
              (agmerr-add x (agmerr-add y z)))
       (equal (agmerr-mul (agmerr-mul x y) z)
              (agmerr-mul x (agmerr-mul y z)))
       (equal (agmerr-mul x (agmerr-add y z))
              (agmerr-add
               (agmerr-mul x y)
               (agmerr-mul x z))))))))

(defun-sk agmerr-order-laws-p ()
  (forall (x y z)
    (implies
     (and (agmerr-real-p x)
          (agmerr-real-p y)
          (agmerr-real-p z))
     (and
      (not (agmerr-lt x x))
      (or (equal x y)
          (agmerr-lt x y)
          (agmerr-lt y x))
      (implies
       (and (agmerr-lt x y)
            (agmerr-lt y z))
       (agmerr-lt x z))
      (implies
       (agmerr-lt x y)
       (agmerr-lt
        (agmerr-add x z)
        (agmerr-add y z)))
      (implies
       (and (agmerr-lt (agmerr-zero) x)
            (agmerr-lt (agmerr-zero) y))
       (agmerr-lt
        (agmerr-zero)
        (agmerr-mul x y)))))))

(defun-sk agmerr-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (agmerr-real-p (agmerr-of-rational a))
      (equal (agmerr-of-rational 0) (agmerr-zero))
      (equal (agmerr-of-rational 1) (agmerr-one))
      (equal
       (agmerr-of-rational (+ a b))
       (agmerr-add
        (agmerr-of-rational a)
        (agmerr-of-rational b)))
      (equal
       (agmerr-of-rational (* a b))
       (agmerr-mul
        (agmerr-of-rational a)
        (agmerr-of-rational b)))
      (equal
       (agmerr-of-rational (- a))
       (agmerr-neg (agmerr-of-rational a)))
      (iff
       (equal a b)
       (equal
        (agmerr-of-rational a)
        (agmerr-of-rational b)))
      (iff
       (< a b)
       (agmerr-lt
        (agmerr-of-rational a)
        (agmerr-of-rational b)))))))

(defun agmerr-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (agmerr-real-p (car coefficients))
     (agmerr-polynomial-p (cdr coefficients)))))

(defun agmerr-polynomial-value (coefficients x)
  (if (endp coefficients)
      (agmerr-zero)
    (agmerr-add
     (car coefficients)
     (agmerr-mul
      x
      (agmerr-polynomial-value
       (cdr coefficients) x)))))

(defun agmerr-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (agmerr-leading-coefficient (cdr coefficients))))

(defun agmerr-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (agmerr-leading-coefficient coefficients)
     (agmerr-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk agmerr-square-root-exists-p (x)
  (exists (root)
    (and
     (agmerr-nonnegative-p root)
     (equal (agmerr-mul root root) x))))

(defun-sk agmerr-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (agmerr-nonnegative-p x)
     (agmerr-square-root-exists-p x))))

(defun-sk agmerr-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (agmerr-real-p root)
     (equal
      (agmerr-polynomial-value coefficients root)
      (agmerr-zero)))))

(defun-sk agmerr-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (agmerr-polynomial-p coefficients)
      (agmerr-odd-degree-p coefficients))
     (agmerr-polynomial-root-exists-p coefficients))))

(defun agmerr-real-closed-field-p ()
  (and
   (agmerr-field-laws-p)
   (agmerr-order-laws-p)
   (agmerr-rational-laws-p)
   (agmerr-lt (agmerr-zero) (agmerr-one))
   (agmerr-nonnegative-square-roots-p)
   (agmerr-odd-polynomial-roots-p)))

(defun agmerr-principal-square-root-p (root value)
  (and
   (agmerr-nonnegative-p root)
   (equal (agmerr-mul root root) value)))

(defchoose agmerr-sqrt (root) (value)
  (agmerr-principal-square-root-p root value))

        (defun algebra-bleqa-apbon2msqrtableqambsqon8b-statement (a b)
  (implies
   (and
    (agmerr-real-closed-field-p)
    (agmerr-positive-p a)
    (agmerr-positive-p b)
    (agmerr-le b a))
   (agmerr-le
    (agmerr-sub
     (agmerr-div
      (agmerr-add a b)
      (agmerr-of-rational 2))
     (agmerr-sqrt (agmerr-mul a b)))
    (agmerr-div
     (agmerr-pow (agmerr-sub a b) 2)
     (agmerr-mul (agmerr-of-rational 8) b)))))

        (value-triple :itpeval-statement-checked)
        :q
