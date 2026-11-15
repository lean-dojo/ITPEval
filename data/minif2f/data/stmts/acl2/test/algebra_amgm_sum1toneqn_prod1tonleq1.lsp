;; Statement-only formalization of miniF2F artifact algebra_amgm_sum1toneqn_prod1tonleq1:
        ;; a length-n list of nonnegative reals with sum n has product at most one, exactly representing the source finite prefix.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub amgmfin-real-p (value) t)
(defstub amgmfin-zero () t)
(defstub amgmfin-one () t)
(defstub amgmfin-add (left right) t)
(defstub amgmfin-mul (left right) t)
(defstub amgmfin-neg (value) t)
(defstub amgmfin-inv (value) t)
(defstub amgmfin-lt (left right) t)
(defstub amgmfin-of-rational (value) t)

(defun amgmfin-sub (left right)
  (amgmfin-add left (amgmfin-neg right)))

(defun amgmfin-div (left right)
  (amgmfin-mul left (amgmfin-inv right)))

(defun amgmfin-le (left right)
  (or (equal left right) (amgmfin-lt left right)))

(defun amgmfin-nonnegative-p (value)
  (and (amgmfin-real-p value)
       (amgmfin-le (amgmfin-zero) value)))

(defun amgmfin-positive-p (value)
  (and (amgmfin-real-p value)
       (amgmfin-lt (amgmfin-zero) value)))

(defun amgmfin-abs (value)
  (if (amgmfin-lt value (amgmfin-zero))
      (amgmfin-neg value)
    value))

(defun amgmfin-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amgmfin-one)
    (amgmfin-mul
     value
     (amgmfin-pow value (1- exponent)))))

(defun-sk amgmfin-field-laws-p ()
  (forall (x y z)
    (and
     (amgmfin-real-p (amgmfin-zero))
     (amgmfin-real-p (amgmfin-one))
     (not (equal (amgmfin-zero) (amgmfin-one)))
     (implies
      (amgmfin-real-p x)
      (and
       (amgmfin-real-p (amgmfin-neg x))
       (amgmfin-real-p (amgmfin-inv x))
       (equal (amgmfin-add x (amgmfin-zero)) x)
       (equal (amgmfin-add x (amgmfin-neg x))
              (amgmfin-zero))
       (equal (amgmfin-mul x (amgmfin-one)) x)
       (implies
        (not (equal x (amgmfin-zero)))
        (equal (amgmfin-mul x (amgmfin-inv x))
               (amgmfin-one)))))
     (equal (amgmfin-inv (amgmfin-zero))
            (amgmfin-zero))
     (implies
      (and (amgmfin-real-p x)
           (amgmfin-real-p y))
      (and
       (amgmfin-real-p (amgmfin-add x y))
       (amgmfin-real-p (amgmfin-mul x y))
       (equal (amgmfin-add x y)
              (amgmfin-add y x))
       (equal (amgmfin-mul x y)
              (amgmfin-mul y x))))
     (implies
      (and (amgmfin-real-p x)
           (amgmfin-real-p y)
           (amgmfin-real-p z))
      (and
       (equal (amgmfin-add (amgmfin-add x y) z)
              (amgmfin-add x (amgmfin-add y z)))
       (equal (amgmfin-mul (amgmfin-mul x y) z)
              (amgmfin-mul x (amgmfin-mul y z)))
       (equal (amgmfin-mul x (amgmfin-add y z))
              (amgmfin-add
               (amgmfin-mul x y)
               (amgmfin-mul x z))))))))

(defun-sk amgmfin-order-laws-p ()
  (forall (x y z)
    (implies
     (and (amgmfin-real-p x)
          (amgmfin-real-p y)
          (amgmfin-real-p z))
     (and
      (not (amgmfin-lt x x))
      (or (equal x y)
          (amgmfin-lt x y)
          (amgmfin-lt y x))
      (implies
       (and (amgmfin-lt x y)
            (amgmfin-lt y z))
       (amgmfin-lt x z))
      (implies
       (amgmfin-lt x y)
       (amgmfin-lt
        (amgmfin-add x z)
        (amgmfin-add y z)))
      (implies
       (and (amgmfin-lt (amgmfin-zero) x)
            (amgmfin-lt (amgmfin-zero) y))
       (amgmfin-lt
        (amgmfin-zero)
        (amgmfin-mul x y)))))))

(defun-sk amgmfin-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (amgmfin-real-p (amgmfin-of-rational a))
      (equal (amgmfin-of-rational 0) (amgmfin-zero))
      (equal (amgmfin-of-rational 1) (amgmfin-one))
      (equal
       (amgmfin-of-rational (+ a b))
       (amgmfin-add
        (amgmfin-of-rational a)
        (amgmfin-of-rational b)))
      (equal
       (amgmfin-of-rational (* a b))
       (amgmfin-mul
        (amgmfin-of-rational a)
        (amgmfin-of-rational b)))
      (equal
       (amgmfin-of-rational (- a))
       (amgmfin-neg (amgmfin-of-rational a)))
      (iff
       (equal a b)
       (equal
        (amgmfin-of-rational a)
        (amgmfin-of-rational b)))
      (iff
       (< a b)
       (amgmfin-lt
        (amgmfin-of-rational a)
        (amgmfin-of-rational b)))))))

(defun amgmfin-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amgmfin-real-p (car coefficients))
     (amgmfin-polynomial-p (cdr coefficients)))))

(defun amgmfin-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amgmfin-zero)
    (amgmfin-add
     (car coefficients)
     (amgmfin-mul
      x
      (amgmfin-polynomial-value
       (cdr coefficients) x)))))

(defun amgmfin-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amgmfin-leading-coefficient (cdr coefficients))))

(defun amgmfin-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amgmfin-leading-coefficient coefficients)
     (amgmfin-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amgmfin-square-root-exists-p (x)
  (exists (root)
    (and
     (amgmfin-nonnegative-p root)
     (equal (amgmfin-mul root root) x))))

(defun-sk amgmfin-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (amgmfin-nonnegative-p x)
     (amgmfin-square-root-exists-p x))))

(defun-sk amgmfin-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (amgmfin-real-p root)
     (equal
      (amgmfin-polynomial-value coefficients root)
      (amgmfin-zero)))))

(defun-sk amgmfin-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amgmfin-polynomial-p coefficients)
      (amgmfin-odd-degree-p coefficients))
     (amgmfin-polynomial-root-exists-p coefficients))))

(defun amgmfin-real-closed-field-p ()
  (and
   (amgmfin-field-laws-p)
   (amgmfin-order-laws-p)
   (amgmfin-rational-laws-p)
   (amgmfin-lt (amgmfin-zero) (amgmfin-one))
   (amgmfin-nonnegative-square-roots-p)
   (amgmfin-odd-polynomial-roots-p)))

(defun amgmfin-principal-square-root-p (root value)
  (and
   (amgmfin-nonnegative-p root)
   (equal (amgmfin-mul root root) value)))

(defchoose amgmfin-sqrt (root) (value)
  (amgmfin-principal-square-root-p root value))

        (defun amgmfin-nonnegative-real-list-p (values)
  (if (endp values)
      (equal values nil)
    (and
     (amgmfin-nonnegative-p (car values))
     (amgmfin-nonnegative-real-list-p (cdr values)))))

(defun amgmfin-sum (values)
  (if (endp values)
      (amgmfin-zero)
    (amgmfin-add
     (car values)
     (amgmfin-sum (cdr values)))))

(defun amgmfin-product (values)
  (if (endp values)
      (amgmfin-one)
    (amgmfin-mul
     (car values)
     (amgmfin-product (cdr values)))))

(defun algebra-amgm-sum1toneqn-prod1tonleq1-statement (values n)
  (implies
   (and
    (amgmfin-real-closed-field-p)
    (natp n)
    (true-listp values)
    (equal (len values) n)
    (amgmfin-nonnegative-real-list-p values)
    (equal
     (amgmfin-sum values)
     (amgmfin-of-rational n)))
   (amgmfin-le
    (amgmfin-product values)
    (amgmfin-one))))

        (value-triple :itpeval-statement-checked)
        :q
