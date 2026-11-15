;; Statement-only formalization of miniF2F artifact amc12a_2013_p7:
        ;; a real Fibonacci-recurrence sequence with s(9)=110 and s(7)=42 has s(4)=10.
        ;; This file contains no proof.
        ;;
        ;; The operation symbols below present an arbitrary real-closed ordered
        ;; field. Every field, order, rational-embedding, and real-closedness law
        ;; is an explicit premise of the statement. By first-order transfer this
        ;; preserves the source proposition over the real numbers without
        ;; restricting variables to ACL2's executable rationals.

        (in-package "ACL2")

        (set-inhibit-output-lst '(prove proof-tree event summary))

        (defstub amca13p7-real-p (value) t)
(defstub amca13p7-zero () t)
(defstub amca13p7-one () t)
(defstub amca13p7-add (left right) t)
(defstub amca13p7-mul (left right) t)
(defstub amca13p7-neg (value) t)
(defstub amca13p7-inv (value) t)
(defstub amca13p7-lt (left right) t)
(defstub amca13p7-of-rational (value) t)

(defun amca13p7-sub (left right)
  (amca13p7-add left (amca13p7-neg right)))

(defun amca13p7-div (left right)
  (amca13p7-mul left (amca13p7-inv right)))

(defun amca13p7-le (left right)
  (or (equal left right) (amca13p7-lt left right)))

(defun amca13p7-nonnegative-p (value)
  (and (amca13p7-real-p value)
       (amca13p7-le (amca13p7-zero) value)))

(defun amca13p7-positive-p (value)
  (and (amca13p7-real-p value)
       (amca13p7-lt (amca13p7-zero) value)))

(defun amca13p7-abs (value)
  (if (amca13p7-lt value (amca13p7-zero))
      (amca13p7-neg value)
    value))

(defun amca13p7-pow (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (amca13p7-one)
    (amca13p7-mul
     value
     (amca13p7-pow value (1- exponent)))))

(defun-sk amca13p7-field-laws-p ()
  (forall (x y z)
    (and
     (amca13p7-real-p (amca13p7-zero))
     (amca13p7-real-p (amca13p7-one))
     (not (equal (amca13p7-zero) (amca13p7-one)))
     (implies
      (amca13p7-real-p x)
      (and
       (amca13p7-real-p (amca13p7-neg x))
       (amca13p7-real-p (amca13p7-inv x))
       (equal (amca13p7-add x (amca13p7-zero)) x)
       (equal (amca13p7-add x (amca13p7-neg x))
              (amca13p7-zero))
       (equal (amca13p7-mul x (amca13p7-one)) x)
       (implies
        (not (equal x (amca13p7-zero)))
        (equal (amca13p7-mul x (amca13p7-inv x))
               (amca13p7-one)))))
     (equal (amca13p7-inv (amca13p7-zero))
            (amca13p7-zero))
     (implies
      (and (amca13p7-real-p x)
           (amca13p7-real-p y))
      (and
       (amca13p7-real-p (amca13p7-add x y))
       (amca13p7-real-p (amca13p7-mul x y))
       (equal (amca13p7-add x y)
              (amca13p7-add y x))
       (equal (amca13p7-mul x y)
              (amca13p7-mul y x))))
     (implies
      (and (amca13p7-real-p x)
           (amca13p7-real-p y)
           (amca13p7-real-p z))
      (and
       (equal (amca13p7-add (amca13p7-add x y) z)
              (amca13p7-add x (amca13p7-add y z)))
       (equal (amca13p7-mul (amca13p7-mul x y) z)
              (amca13p7-mul x (amca13p7-mul y z)))
       (equal (amca13p7-mul x (amca13p7-add y z))
              (amca13p7-add
               (amca13p7-mul x y)
               (amca13p7-mul x z))))))))

(defun-sk amca13p7-order-laws-p ()
  (forall (x y z)
    (implies
     (and (amca13p7-real-p x)
          (amca13p7-real-p y)
          (amca13p7-real-p z))
     (and
      (not (amca13p7-lt x x))
      (or (equal x y)
          (amca13p7-lt x y)
          (amca13p7-lt y x))
      (implies
       (and (amca13p7-lt x y)
            (amca13p7-lt y z))
       (amca13p7-lt x z))
      (implies
       (amca13p7-lt x y)
       (amca13p7-lt
        (amca13p7-add x z)
        (amca13p7-add y z)))
      (implies
       (and (amca13p7-lt (amca13p7-zero) x)
            (amca13p7-lt (amca13p7-zero) y))
       (amca13p7-lt
        (amca13p7-zero)
        (amca13p7-mul x y)))))))

(defun-sk amca13p7-rational-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (amca13p7-real-p (amca13p7-of-rational a))
      (equal (amca13p7-of-rational 0) (amca13p7-zero))
      (equal (amca13p7-of-rational 1) (amca13p7-one))
      (equal
       (amca13p7-of-rational (+ a b))
       (amca13p7-add
        (amca13p7-of-rational a)
        (amca13p7-of-rational b)))
      (equal
       (amca13p7-of-rational (* a b))
       (amca13p7-mul
        (amca13p7-of-rational a)
        (amca13p7-of-rational b)))
      (equal
       (amca13p7-of-rational (- a))
       (amca13p7-neg (amca13p7-of-rational a)))
      (iff
       (equal a b)
       (equal
        (amca13p7-of-rational a)
        (amca13p7-of-rational b)))
      (iff
       (< a b)
       (amca13p7-lt
        (amca13p7-of-rational a)
        (amca13p7-of-rational b)))))))

(defun amca13p7-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (amca13p7-real-p (car coefficients))
     (amca13p7-polynomial-p (cdr coefficients)))))

(defun amca13p7-polynomial-value (coefficients x)
  (if (endp coefficients)
      (amca13p7-zero)
    (amca13p7-add
     (car coefficients)
     (amca13p7-mul
      x
      (amca13p7-polynomial-value
       (cdr coefficients) x)))))

(defun amca13p7-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amca13p7-leading-coefficient (cdr coefficients))))

(defun amca13p7-odd-degree-p (coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amca13p7-leading-coefficient coefficients)
     (amca13p7-zero)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amca13p7-square-root-exists-p (x)
  (exists (root)
    (and
     (amca13p7-nonnegative-p root)
     (equal (amca13p7-mul root root) x))))

(defun-sk amca13p7-nonnegative-square-roots-p ()
  (forall (x)
    (implies
     (amca13p7-nonnegative-p x)
     (amca13p7-square-root-exists-p x))))

(defun-sk amca13p7-polynomial-root-exists-p (coefficients)
  (exists (root)
    (and
     (amca13p7-real-p root)
     (equal
      (amca13p7-polynomial-value coefficients root)
      (amca13p7-zero)))))

(defun-sk amca13p7-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amca13p7-polynomial-p coefficients)
      (amca13p7-odd-degree-p coefficients))
     (amca13p7-polynomial-root-exists-p coefficients))))

(defun amca13p7-real-closed-field-p ()
  (and
   (amca13p7-field-laws-p)
   (amca13p7-order-laws-p)
   (amca13p7-rational-laws-p)
   (amca13p7-lt (amca13p7-zero) (amca13p7-one))
   (amca13p7-nonnegative-square-roots-p)
   (amca13p7-odd-polynomial-roots-p)))

(defun amca13p7-principal-square-root-p (root value)
  (and
   (amca13p7-nonnegative-p root)
   (equal (amca13p7-mul root root) value)))

(defchoose amca13p7-sqrt (root) (value)
  (amca13p7-principal-square-root-p root value))

        (defun amca13p7-sequence-value (s0 s1 index)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      s0
    (if (equal index 1)
        s1
      (amca13p7-add
       (amca13p7-sequence-value s0 s1 (1- index))
       (amca13p7-sequence-value s0 s1 (- index 2))))))

(defun amc12a-2013-p7-statement (s0 s1)
  (implies
   (and
    (amca13p7-real-closed-field-p)
    (amca13p7-real-p s0)
    (amca13p7-real-p s1)
    (equal
     (amca13p7-sequence-value s0 s1 9)
     (amca13p7-of-rational 110))
    (equal
     (amca13p7-sequence-value s0 s1 7)
     (amca13p7-of-rational 42)))
   (equal
    (amca13p7-sequence-value s0 s1 4)
    (amca13p7-of-rational 10))))

        (value-triple :itpeval-statement-checked)
        :q
