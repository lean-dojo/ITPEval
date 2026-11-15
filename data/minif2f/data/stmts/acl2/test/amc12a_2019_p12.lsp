;; Statement-only formalization of miniF2F artifact amc12a_2019_p12:
        ;; after the bijective substitutions u=log_2(x), v=log_2(y), the two source logarithmic hypotheses imply (u-v)^2=20.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub amca19p12-real-p (value) t)
(defstub amca19p12-zero () t)
(defstub amca19p12-one () t)
(defstub amca19p12-add (left right) t)
(defstub amca19p12-mul (left right) t)
(defstub amca19p12-neg (value) t)
(defstub amca19p12-inv (value) t)
(defstub amca19p12-lt (left right) t)
(defstub amca19p12-of-rational (value) t)

(defun amca19p12-sub (left right)
  (amca19p12-add left (amca19p12-neg right)))

(defun amca19p12-div (left right)
  (amca19p12-mul left (amca19p12-inv right)))

(defun amca19p12-le (left right)
  (or (equal left right) (amca19p12-lt left right)))

(defun amca19p12-nonnegative-p (value)
  (and (amca19p12-real-p value)
       (amca19p12-le (amca19p12-zero) value)))

(defun amca19p12-positive-p (value)
  (and (amca19p12-real-p value)
       (amca19p12-lt (amca19p12-zero) value)))

(defun amca19p12-abs (value)
  (if (amca19p12-lt value (amca19p12-zero))
      (amca19p12-neg value)
    value))

(defun amca19p12-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amca19p12-one)
    (amca19p12-mul
     value
     (amca19p12-pow value (1- exponent)))))

(defun-sk amca19p12-field-laws-p ()
  (forall (x y z)
    (and
     (amca19p12-real-p (amca19p12-zero))
     (amca19p12-real-p (amca19p12-one))
     (not (equal (amca19p12-zero) (amca19p12-one)))
     (implies
      (amca19p12-real-p x)
      (and
       (amca19p12-real-p (amca19p12-neg x))
       (amca19p12-real-p (amca19p12-inv x))
       (equal (amca19p12-add x (amca19p12-zero)) x)
       (equal (amca19p12-add x (amca19p12-neg x))
              (amca19p12-zero))
       (equal (amca19p12-mul x (amca19p12-one)) x)
       (implies
        (not (equal x (amca19p12-zero)))
        (equal (amca19p12-mul x (amca19p12-inv x))
               (amca19p12-one)))))
     (equal (amca19p12-inv (amca19p12-zero))
            (amca19p12-zero))
     (implies
      (and (amca19p12-real-p x)
           (amca19p12-real-p y))
      (and
       (amca19p12-real-p (amca19p12-add x y))
       (amca19p12-real-p (amca19p12-mul x y))
       (equal (amca19p12-add x y)
              (amca19p12-add y x))
       (equal (amca19p12-mul x y)
              (amca19p12-mul y x))))
     (implies
      (and (amca19p12-real-p x)
           (amca19p12-real-p y)
           (amca19p12-real-p z))
      (and
       (equal (amca19p12-add (amca19p12-add x y) z)
              (amca19p12-add x (amca19p12-add y z)))
       (equal (amca19p12-mul (amca19p12-mul x y) z)
              (amca19p12-mul x (amca19p12-mul y z)))
       (equal (amca19p12-mul x (amca19p12-add y z))
              (amca19p12-add
               (amca19p12-mul x y)
               (amca19p12-mul x z))))))))

(defun-sk amca19p12-order-laws-p ()
  (forall (x y z)
    (implies
     (and (amca19p12-real-p x)
          (amca19p12-real-p y)
          (amca19p12-real-p z))
     (and
      (not (amca19p12-lt x x))
      (or (equal x y)
          (amca19p12-lt x y)
          (amca19p12-lt y x))
      (implies
       (and (amca19p12-lt x y)
            (amca19p12-lt y z))
       (amca19p12-lt x z))
      (implies
       (amca19p12-lt x y)
       (amca19p12-lt
        (amca19p12-add x z)
        (amca19p12-add y z)))
      (implies
       (and (amca19p12-lt (amca19p12-zero) x)
            (amca19p12-lt (amca19p12-zero) y))
       (amca19p12-lt
        (amca19p12-zero)
        (amca19p12-mul x y)))))))

(defun-sk amca19p12-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (amca19p12-real-p (amca19p12-of-rational a))
      (equal (amca19p12-of-rational 0) (amca19p12-zero))
      (equal (amca19p12-of-rational 1) (amca19p12-one))
      (equal
       (amca19p12-of-rational (+ a b))
       (amca19p12-add
        (amca19p12-of-rational a)
        (amca19p12-of-rational b)))
      (equal
       (amca19p12-of-rational (* a b))
       (amca19p12-mul
        (amca19p12-of-rational a)
        (amca19p12-of-rational b)))
      (equal
       (amca19p12-of-rational (- a))
       (amca19p12-neg (amca19p12-of-rational a)))
      (iff
       (equal a b)
       (equal
        (amca19p12-of-rational a)
        (amca19p12-of-rational b)))
      (iff
       (< a b)
       (amca19p12-lt
        (amca19p12-of-rational a)
        (amca19p12-of-rational b)))))))

(defun amca19p12-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amca19p12-real-p (car coefficients))
     (amca19p12-polynomial-p (cdr coefficients)))))

(defun amca19p12-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amca19p12-zero)
    (amca19p12-add
     (car coefficients)
     (amca19p12-mul
      x
      (amca19p12-polynomial-value
       (cdr coefficients) x)))))

(defun amca19p12-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amca19p12-leading-coefficient (cdr coefficients))))

(defun amca19p12-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amca19p12-leading-coefficient coefficients)
     (amca19p12-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amca19p12-square-root-exists-p (x)
  (exists (root)
    (and
     (amca19p12-nonnegative-p root)
     (equal (amca19p12-mul root root) x))))

(defun-sk amca19p12-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (amca19p12-nonnegative-p x)
     (amca19p12-square-root-exists-p x))))

(defun-sk amca19p12-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (amca19p12-real-p root)
     (equal
      (amca19p12-polynomial-value coefficients root)
      (amca19p12-zero)))))

(defun-sk amca19p12-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amca19p12-polynomial-p coefficients)
      (amca19p12-odd-degree-p coefficients))
     (amca19p12-polynomial-root-exists-p coefficients))))

(defun amca19p12-real-closed-field-p ()
  (and
   (amca19p12-field-laws-p)
   (amca19p12-order-laws-p)
   (amca19p12-rational-laws-p)
   (amca19p12-lt (amca19p12-zero) (amca19p12-one))
   (amca19p12-nonnegative-square-roots-p)
   (amca19p12-odd-polynomial-roots-p)))

(defun amca19p12-principal-square-root-p (root value)
  (and
   (amca19p12-nonnegative-p root)
   (equal (amca19p12-mul root root) value)))

(defchoose amca19p12-sqrt (root) (value)
  (amca19p12-principal-square-root-p root value))

        (defun amc12a-2019-p12-statement (u v)
  (implies
   (and
    (amca19p12-real-closed-field-p)
    (amca19p12-real-p u)
    (amca19p12-real-p v)
    (not (equal u (amca19p12-zero)))
    (not (equal v (amca19p12-zero)))
    (equal
     u
     (amca19p12-div
      (amca19p12-of-rational 4) v))
    (equal
     (amca19p12-add u v)
     (amca19p12-of-rational 6)))
   (equal
    (amca19p12-pow
     (amca19p12-sub u v) 2)
    (amca19p12-of-rational 20))))

        (value-triple :itpeval-statement-checked)
        :q
