;; Statement-only formalization of Hundred Theorems artifact 091, "The
;; Triangle Inequality": in an inner-product space over an arbitrary strict
;; ordered field, the norm of x+y is at most the sum of the norms.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub ht091-scalar-p (x) t)
(defstub ht091-add-op (x y) t)
(defstub ht091-multiply-op (x y) t)
(defstub ht091-negate-op (x) t)
(defstub ht091-inverse-op (x) t)
(defstub ht091-less-op (x y) t)
(defstub ht091-vector-p (x) t)
(defstub ht091-vector-add-op (x y) t)
(defstub ht091-vector-negate-op (x) t)
(defstub ht091-scalar-multiply-op (a x) t)
(defstub ht091-inner-op (x y) t)

(defun ht091-scalar-member-p (x)
  (if (ht091-scalar-p x) t nil))

(defun ht091-add (x y)
  (ht091-add-op x y))

(defun ht091-mul (x y)
  (ht091-multiply-op x y))

(defun ht091-neg (x)
  (ht091-negate-op x))

(defun ht091-inv (x)
  (ht091-inverse-op x))

(defun ht091-less (x y)
  (if (ht091-less-op x y) t nil))

(defun ht091-leq (x y)
  (not (ht091-less y x)))

(defun ht091-vector-member-p (x)
  (if (ht091-vector-p x) t nil))

(defun ht091-vadd (x y)
  (ht091-vector-add-op x y))

(defun ht091-vneg (x)
  (ht091-vector-negate-op x))

(defun ht091-smul (a x)
  (ht091-scalar-multiply-op a x))

(defun ht091-inner (x y)
  (ht091-inner-op x y))

(defun-sk ht091-field-laws-p (zero one)
  (forall (a b c)
    (implies
     (and
      (ht091-scalar-member-p a)
      (ht091-scalar-member-p b)
      (ht091-scalar-member-p c))
     (and
      (ht091-scalar-member-p (ht091-add a b))
      (ht091-scalar-member-p (ht091-mul a b))
      (ht091-scalar-member-p (ht091-neg a))
      (ht091-scalar-member-p (ht091-inv a))
      (equal (ht091-add (ht091-add a b) c)
             (ht091-add a (ht091-add b c)))
      (equal (ht091-add a b) (ht091-add b a))
      (equal (ht091-add a zero) a)
      (equal (ht091-add a (ht091-neg a)) zero)
      (equal (ht091-mul (ht091-mul a b) c)
             (ht091-mul a (ht091-mul b c)))
      (equal (ht091-mul a b) (ht091-mul b a))
      (equal (ht091-mul a one) a)
      (equal (ht091-inv zero) zero)
      (implies
       (not (equal a zero))
       (equal (ht091-mul a (ht091-inv a)) one))
      (equal
       (ht091-mul a (ht091-add b c))
       (ht091-add (ht091-mul a b)
                  (ht091-mul a c)))))))

(defun-sk ht091-order-laws-p (zero)
  (forall (a b c)
    (implies
     (and
      (ht091-scalar-member-p a)
      (ht091-scalar-member-p b)
      (ht091-scalar-member-p c))
     (and
      (not (ht091-less a a))
      (or (equal a b)
          (ht091-less a b)
          (ht091-less b a))
      (implies
       (and (ht091-less a b)
            (ht091-less b c))
       (ht091-less a c))
      (implies
       (ht091-less a b)
       (ht091-less (ht091-add a c)
                   (ht091-add b c)))
      (implies
       (and (ht091-less zero a)
            (ht091-less zero b))
       (ht091-less zero (ht091-mul a b)))))))

(defun ht091-ordered-field-p (zero one)
  (and
   (ht091-scalar-member-p zero)
   (ht091-scalar-member-p one)
   (not (equal zero one))
   (ht091-less zero one)
   (ht091-field-laws-p zero one)
   (ht091-order-laws-p zero)))

(defun-sk ht091-vector-space-laws-p (zero one vector-zero)
  (forall (a b x y z)
    (implies
     (and
      (ht091-scalar-member-p a)
      (ht091-scalar-member-p b)
      (ht091-vector-member-p x)
      (ht091-vector-member-p y)
      (ht091-vector-member-p z))
     (and
      (ht091-vector-member-p (ht091-vadd x y))
      (ht091-vector-member-p (ht091-vneg x))
      (ht091-vector-member-p (ht091-smul a x))
      (equal (ht091-vadd (ht091-vadd x y) z)
             (ht091-vadd x (ht091-vadd y z)))
      (equal (ht091-vadd x y) (ht091-vadd y x))
      (equal (ht091-vadd x vector-zero) x)
      (equal (ht091-vadd x (ht091-vneg x)) vector-zero)
      (equal (ht091-smul one x) x)
      (equal (ht091-smul (ht091-mul a b) x)
             (ht091-smul a (ht091-smul b x)))
      (equal (ht091-smul a (ht091-vadd x y))
             (ht091-vadd (ht091-smul a x)
                         (ht091-smul a y)))
      (equal (ht091-smul (ht091-add a b) x)
             (ht091-vadd (ht091-smul a x)
                         (ht091-smul b x)))
      (equal (ht091-smul zero x) vector-zero)))))

(defun-sk ht091-inner-product-laws-p (zero)
  (forall (a x y z)
    (implies
     (and
      (ht091-scalar-member-p a)
      (ht091-vector-member-p x)
      (ht091-vector-member-p y)
      (ht091-vector-member-p z))
     (and
      (ht091-scalar-member-p (ht091-inner x y))
      (equal (ht091-inner x y)
             (ht091-inner y x))
      (equal (ht091-inner (ht091-vadd x y) z)
             (ht091-add (ht091-inner x z)
                        (ht091-inner y z)))
      (equal (ht091-inner (ht091-smul a x) y)
             (ht091-mul a (ht091-inner x y)))
      (ht091-leq zero (ht091-inner x x))
      (implies
       (equal (ht091-inner x x) zero)
       (equal x (ht091-smul zero x)))))))

(defun ht091-inner-product-space-p (zero one vector-zero)
  (and
   (ht091-ordered-field-p zero one)
   (ht091-vector-member-p vector-zero)
   (ht091-vector-space-laws-p zero one vector-zero)
   (ht091-inner-product-laws-p zero)))

(defun hundred-theorems-091-triangle-inequality-statement
    (zero one vector-zero x y norm-x norm-y norm-sum)
  (implies
   (and
    (ht091-inner-product-space-p zero one vector-zero)
    (ht091-vector-member-p x)
    (ht091-vector-member-p y)
    (ht091-scalar-member-p norm-x)
    (ht091-scalar-member-p norm-y)
    (ht091-scalar-member-p norm-sum)
    (ht091-leq zero norm-x)
    (ht091-leq zero norm-y)
    (ht091-leq zero norm-sum)
    (equal
     (ht091-mul norm-x norm-x)
     (ht091-inner x x))
    (equal
     (ht091-mul norm-y norm-y)
     (ht091-inner y y))
    (equal
     (ht091-mul norm-sum norm-sum)
     (ht091-inner (ht091-vadd x y)
                  (ht091-vadd x y))))
   (ht091-leq norm-sum
              (ht091-add norm-x norm-y))))

(value-triple :itpeval-statement-checked)
:q
