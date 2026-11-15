;; Statement-only formalization of miniF2F artifact imo_1983_p6:
        ;; positive side lengths satisfying the strict triangle inequalities obey the stated cyclic quartic inequality.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub imo83p6-real-p (value) t)
(defstub imo83p6-zero () t)
(defstub imo83p6-one () t)
(defstub imo83p6-add (left right) t)
(defstub imo83p6-mul (left right) t)
(defstub imo83p6-neg (value) t)
(defstub imo83p6-inv (value) t)
(defstub imo83p6-lt (left right) t)
(defstub imo83p6-of-rational (value) t)

(defun imo83p6-sub (left right)
  (imo83p6-add left (imo83p6-neg right)))

(defun imo83p6-div (left right)
  (imo83p6-mul left (imo83p6-inv right)))

(defun imo83p6-le (left right)
  (or (equal left right) (imo83p6-lt left right)))

(defun imo83p6-nonnegative-p (value)
  (and (imo83p6-real-p value)
       (imo83p6-le (imo83p6-zero) value)))

(defun imo83p6-positive-p (value)
  (and (imo83p6-real-p value)
       (imo83p6-lt (imo83p6-zero) value)))

(defun imo83p6-abs (value)
  (if (imo83p6-lt value (imo83p6-zero))
      (imo83p6-neg value)
    value))

(defun imo83p6-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (imo83p6-one)
    (imo83p6-mul
     value
     (imo83p6-pow value (1- exponent)))))

(defun-sk imo83p6-field-laws-p ()
  (forall (x y z)
    (and
     (imo83p6-real-p (imo83p6-zero))
     (imo83p6-real-p (imo83p6-one))
     (not (equal (imo83p6-zero) (imo83p6-one)))
     (implies
      (imo83p6-real-p x)
      (and
       (imo83p6-real-p (imo83p6-neg x))
       (imo83p6-real-p (imo83p6-inv x))
       (equal (imo83p6-add x (imo83p6-zero)) x)
       (equal (imo83p6-add x (imo83p6-neg x))
              (imo83p6-zero))
       (equal (imo83p6-mul x (imo83p6-one)) x)
       (implies
        (not (equal x (imo83p6-zero)))
        (equal (imo83p6-mul x (imo83p6-inv x))
               (imo83p6-one)))))
     (equal (imo83p6-inv (imo83p6-zero))
            (imo83p6-zero))
     (implies
      (and (imo83p6-real-p x)
           (imo83p6-real-p y))
      (and
       (imo83p6-real-p (imo83p6-add x y))
       (imo83p6-real-p (imo83p6-mul x y))
       (equal (imo83p6-add x y)
              (imo83p6-add y x))
       (equal (imo83p6-mul x y)
              (imo83p6-mul y x))))
     (implies
      (and (imo83p6-real-p x)
           (imo83p6-real-p y)
           (imo83p6-real-p z))
      (and
       (equal (imo83p6-add (imo83p6-add x y) z)
              (imo83p6-add x (imo83p6-add y z)))
       (equal (imo83p6-mul (imo83p6-mul x y) z)
              (imo83p6-mul x (imo83p6-mul y z)))
       (equal (imo83p6-mul x (imo83p6-add y z))
              (imo83p6-add
               (imo83p6-mul x y)
               (imo83p6-mul x z))))))))

(defun-sk imo83p6-order-laws-p ()
  (forall (x y z)
    (implies
     (and (imo83p6-real-p x)
          (imo83p6-real-p y)
          (imo83p6-real-p z))
     (and
      (not (imo83p6-lt x x))
      (or (equal x y)
          (imo83p6-lt x y)
          (imo83p6-lt y x))
      (implies
       (and (imo83p6-lt x y)
            (imo83p6-lt y z))
       (imo83p6-lt x z))
      (implies
       (imo83p6-lt x y)
       (imo83p6-lt
        (imo83p6-add x z)
        (imo83p6-add y z)))
      (implies
       (and (imo83p6-lt (imo83p6-zero) x)
            (imo83p6-lt (imo83p6-zero) y))
       (imo83p6-lt
        (imo83p6-zero)
        (imo83p6-mul x y)))))))

(defun-sk imo83p6-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (imo83p6-real-p (imo83p6-of-rational a))
      (equal (imo83p6-of-rational 0) (imo83p6-zero))
      (equal (imo83p6-of-rational 1) (imo83p6-one))
      (equal
       (imo83p6-of-rational (+ a b))
       (imo83p6-add
        (imo83p6-of-rational a)
        (imo83p6-of-rational b)))
      (equal
       (imo83p6-of-rational (* a b))
       (imo83p6-mul
        (imo83p6-of-rational a)
        (imo83p6-of-rational b)))
      (equal
       (imo83p6-of-rational (- a))
       (imo83p6-neg (imo83p6-of-rational a)))
      (iff
       (equal a b)
       (equal
        (imo83p6-of-rational a)
        (imo83p6-of-rational b)))
      (iff
       (< a b)
       (imo83p6-lt
        (imo83p6-of-rational a)
        (imo83p6-of-rational b)))))))

(defun imo83p6-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (imo83p6-real-p (car coefficients))
     (imo83p6-polynomial-p (cdr coefficients)))))

(defun imo83p6-polynomial-value (coefficients x)
  (if (endp coefficients)
      (imo83p6-zero)
    (imo83p6-add
     (car coefficients)
     (imo83p6-mul
      x
      (imo83p6-polynomial-value
       (cdr coefficients) x)))))

(defun imo83p6-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (imo83p6-leading-coefficient (cdr coefficients))))

(defun imo83p6-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (imo83p6-leading-coefficient coefficients)
     (imo83p6-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk imo83p6-square-root-exists-p (x)
  (exists (root)
    (and
     (imo83p6-nonnegative-p root)
     (equal (imo83p6-mul root root) x))))

(defun-sk imo83p6-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (imo83p6-nonnegative-p x)
     (imo83p6-square-root-exists-p x))))

(defun-sk imo83p6-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (imo83p6-real-p root)
     (equal
      (imo83p6-polynomial-value coefficients root)
      (imo83p6-zero)))))

(defun-sk imo83p6-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (imo83p6-polynomial-p coefficients)
      (imo83p6-odd-degree-p coefficients))
     (imo83p6-polynomial-root-exists-p coefficients))))

(defun imo83p6-real-closed-field-p ()
  (and
   (imo83p6-field-laws-p)
   (imo83p6-order-laws-p)
   (imo83p6-rational-laws-p)
   (imo83p6-lt (imo83p6-zero) (imo83p6-one))
   (imo83p6-nonnegative-square-roots-p)
   (imo83p6-odd-polynomial-roots-p)))

(defun imo83p6-principal-square-root-p (root value)
  (and
   (imo83p6-nonnegative-p root)
   (equal (imo83p6-mul root root) value)))

(defchoose imo83p6-sqrt (root) (value)
  (imo83p6-principal-square-root-p root value))

        (defun imo-1983-p6-statement (a b c)
  (implies
   (and
    (imo83p6-real-closed-field-p)
    (imo83p6-positive-p a)
    (imo83p6-positive-p b)
    (imo83p6-positive-p c)
    (imo83p6-lt c (imo83p6-add a b))
    (imo83p6-lt b (imo83p6-add a c))
    (imo83p6-lt a (imo83p6-add b c)))
   (imo83p6-le
    (imo83p6-zero)
    (imo83p6-add
     (imo83p6-add
      (imo83p6-mul
       (imo83p6-mul (imo83p6-pow a 2) b)
       (imo83p6-sub a b))
      (imo83p6-mul
       (imo83p6-mul (imo83p6-pow b 2) c)
       (imo83p6-sub b c)))
     (imo83p6-mul
      (imo83p6-mul (imo83p6-pow c 2) a)
      (imo83p6-sub c a))))))

        (value-triple :itpeval-statement-checked)
        :q
