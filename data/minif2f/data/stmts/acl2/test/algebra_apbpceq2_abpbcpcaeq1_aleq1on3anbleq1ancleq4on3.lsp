;; Statement-only formalization of miniF2F artifact algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3:
        ;; ordered real a, b, c with a+b+c=2 and ab+bc+ca=1 satisfy the six stated interval bounds.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub abc213-real-p (value) t)
(defstub abc213-zero () t)
(defstub abc213-one () t)
(defstub abc213-add (left right) t)
(defstub abc213-mul (left right) t)
(defstub abc213-neg (value) t)
(defstub abc213-inv (value) t)
(defstub abc213-lt (left right) t)
(defstub abc213-of-rational (value) t)

(defun abc213-sub (left right)
  (abc213-add left (abc213-neg right)))

(defun abc213-div (left right)
  (abc213-mul left (abc213-inv right)))

(defun abc213-le (left right)
  (or (equal left right) (abc213-lt left right)))

(defun abc213-nonnegative-p (value)
  (and (abc213-real-p value)
       (abc213-le (abc213-zero) value)))

(defun abc213-positive-p (value)
  (and (abc213-real-p value)
       (abc213-lt (abc213-zero) value)))

(defun abc213-abs (value)
  (if (abc213-lt value (abc213-zero))
      (abc213-neg value)
    value))

(defun abc213-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (abc213-one)
    (abc213-mul
     value
     (abc213-pow value (1- exponent)))))

(defun-sk abc213-field-laws-p ()
  (forall (x y z)
    (and
     (abc213-real-p (abc213-zero))
     (abc213-real-p (abc213-one))
     (not (equal (abc213-zero) (abc213-one)))
     (implies
      (abc213-real-p x)
      (and
       (abc213-real-p (abc213-neg x))
       (abc213-real-p (abc213-inv x))
       (equal (abc213-add x (abc213-zero)) x)
       (equal (abc213-add x (abc213-neg x))
              (abc213-zero))
       (equal (abc213-mul x (abc213-one)) x)
       (implies
        (not (equal x (abc213-zero)))
        (equal (abc213-mul x (abc213-inv x))
               (abc213-one)))))
     (equal (abc213-inv (abc213-zero))
            (abc213-zero))
     (implies
      (and (abc213-real-p x)
           (abc213-real-p y))
      (and
       (abc213-real-p (abc213-add x y))
       (abc213-real-p (abc213-mul x y))
       (equal (abc213-add x y)
              (abc213-add y x))
       (equal (abc213-mul x y)
              (abc213-mul y x))))
     (implies
      (and (abc213-real-p x)
           (abc213-real-p y)
           (abc213-real-p z))
      (and
       (equal (abc213-add (abc213-add x y) z)
              (abc213-add x (abc213-add y z)))
       (equal (abc213-mul (abc213-mul x y) z)
              (abc213-mul x (abc213-mul y z)))
       (equal (abc213-mul x (abc213-add y z))
              (abc213-add
               (abc213-mul x y)
               (abc213-mul x z))))))))

(defun-sk abc213-order-laws-p ()
  (forall (x y z)
    (implies
     (and (abc213-real-p x)
          (abc213-real-p y)
          (abc213-real-p z))
     (and
      (not (abc213-lt x x))
      (or (equal x y)
          (abc213-lt x y)
          (abc213-lt y x))
      (implies
       (and (abc213-lt x y)
            (abc213-lt y z))
       (abc213-lt x z))
      (implies
       (abc213-lt x y)
       (abc213-lt
        (abc213-add x z)
        (abc213-add y z)))
      (implies
       (and (abc213-lt (abc213-zero) x)
            (abc213-lt (abc213-zero) y))
       (abc213-lt
        (abc213-zero)
        (abc213-mul x y)))))))

(defun-sk abc213-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (abc213-real-p (abc213-of-rational a))
      (equal (abc213-of-rational 0) (abc213-zero))
      (equal (abc213-of-rational 1) (abc213-one))
      (equal
       (abc213-of-rational (+ a b))
       (abc213-add
        (abc213-of-rational a)
        (abc213-of-rational b)))
      (equal
       (abc213-of-rational (* a b))
       (abc213-mul
        (abc213-of-rational a)
        (abc213-of-rational b)))
      (equal
       (abc213-of-rational (- a))
       (abc213-neg (abc213-of-rational a)))
      (iff
       (equal a b)
       (equal
        (abc213-of-rational a)
        (abc213-of-rational b)))
      (iff
       (< a b)
       (abc213-lt
        (abc213-of-rational a)
        (abc213-of-rational b)))))))

(defun abc213-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (abc213-real-p (car coefficients))
     (abc213-polynomial-p (cdr coefficients)))))

(defun abc213-polynomial-value (coefficients x)
  (if (endp coefficients)
      (abc213-zero)
    (abc213-add
     (car coefficients)
     (abc213-mul
      x
      (abc213-polynomial-value
       (cdr coefficients) x)))))

(defun abc213-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (abc213-leading-coefficient (cdr coefficients))))

(defun abc213-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (abc213-leading-coefficient coefficients)
     (abc213-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk abc213-square-root-exists-p (x)
  (exists (root)
    (and
     (abc213-nonnegative-p root)
     (equal (abc213-mul root root) x))))

(defun-sk abc213-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (abc213-nonnegative-p x)
     (abc213-square-root-exists-p x))))

(defun-sk abc213-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (abc213-real-p root)
     (equal
      (abc213-polynomial-value coefficients root)
      (abc213-zero)))))

(defun-sk abc213-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (abc213-polynomial-p coefficients)
      (abc213-odd-degree-p coefficients))
     (abc213-polynomial-root-exists-p coefficients))))

(defun abc213-real-closed-field-p ()
  (and
   (abc213-field-laws-p)
   (abc213-order-laws-p)
   (abc213-rational-laws-p)
   (abc213-lt (abc213-zero) (abc213-one))
   (abc213-nonnegative-square-roots-p)
   (abc213-odd-polynomial-roots-p)))

(defun abc213-principal-square-root-p (root value)
  (and
   (abc213-nonnegative-p root)
   (equal (abc213-mul root root) value)))

(defchoose abc213-sqrt (root) (value)
  (abc213-principal-square-root-p root value))

        (defun algebra-apbpceq2-abpbcpcaeq1-aleq1on3anbleq1ancleq4on3-statement
    (a b c)
  (implies
   (and
    (abc213-real-closed-field-p)
    (abc213-real-p a)
    (abc213-real-p b)
    (abc213-real-p c)
    (abc213-le a b)
    (abc213-le b c)
    (equal
     (abc213-add (abc213-add a b) c)
     (abc213-of-rational 2))
    (equal
     (abc213-add
      (abc213-add (abc213-mul a b) (abc213-mul b c))
      (abc213-mul c a))
     (abc213-of-rational 1)))
   (and
    (abc213-le (abc213-zero) a)
    (abc213-le a (abc213-of-rational 1/3))
    (abc213-le (abc213-of-rational 1/3) b)
    (abc213-le b (abc213-of-rational 1))
    (abc213-le (abc213-of-rational 1) c)
    (abc213-le c (abc213-of-rational 4/3)))))

        (value-triple :itpeval-statement-checked)
        :q
