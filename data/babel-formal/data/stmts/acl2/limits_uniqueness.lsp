;; Statement-only formalization of Babel-formal artifact limits_uniqueness:
;; uniqueness of a sequence limit in an abstract absolute-valued ordered
;; structure with an arbitrary directed index type. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent arbitrary value and index types,
;; their operations and relations, and an arbitrary sequence. Carrier
;; predicates restrict quantifiers without enumerating either domain.

(defstub limits-uniqueness-r-p (r-type value) t)
(defstub limits-uniqueness-n-p (n-type index) t)

(defstub limits-uniqueness-zero (r-type) t)
(defstub limits-uniqueness-one (r-type) t)
(defstub limits-uniqueness-add (r-type left right) t)
(defstub limits-uniqueness-mul (r-type left right) t)
(defstub limits-uniqueness-opp (r-type value) t)
(defstub limits-uniqueness-abs (r-type value) t)
(defstub limits-uniqueness-le (r-type left right) t)
(defstub limits-uniqueness-lt (r-type left right) t)

(defstub limits-uniqueness-nle (n-type left right) t)
(defstub limits-uniqueness-nmax (n-type left right) t)

(defstub limits-uniqueness-sequence-value
  (r-type n-type sequence index)
  t)

(defun limits-uniqueness-sub (r-type x y)
  (limits-uniqueness-add
   r-type
   x
   (limits-uniqueness-opp r-type y)))

(defun-sk limits-uniqueness-operation-closure-p
    (r-type n-type)
  (forall (x y)
    (and
     (implies
      (limits-uniqueness-r-p r-type x)
      (and
       (limits-uniqueness-r-p
        r-type (limits-uniqueness-opp r-type x))
       (limits-uniqueness-r-p
        r-type (limits-uniqueness-abs r-type x))))
     (implies
      (and
       (limits-uniqueness-r-p r-type x)
       (limits-uniqueness-r-p r-type y))
      (and
       (limits-uniqueness-r-p
        r-type (limits-uniqueness-add r-type x y))
       (limits-uniqueness-r-p
        r-type (limits-uniqueness-mul r-type x y))))
     (implies
      (and
       (limits-uniqueness-n-p n-type x)
       (limits-uniqueness-n-p n-type y))
      (limits-uniqueness-n-p
       n-type (limits-uniqueness-nmax n-type x y))))))

(defun-sk limits-uniqueness-sequence-typed-p
    (r-type n-type sequence)
  (forall (n)
    (implies
     (limits-uniqueness-n-p n-type n)
     (limits-uniqueness-r-p
      r-type
      (limits-uniqueness-sequence-value
       r-type n-type sequence n)))))

(defun-sk limits-uniqueness-directed-p (n-type)
  (forall (x y)
    (implies
     (and
      (limits-uniqueness-n-p n-type x)
      (limits-uniqueness-n-p n-type y))
     (and
      (limits-uniqueness-nle
       n-type x (limits-uniqueness-nmax n-type x y))
      (limits-uniqueness-nle
       n-type y (limits-uniqueness-nmax n-type x y))))))

(defun-sk limits-uniqueness-unary-laws-p (r-type)
  (forall (x)
    (implies
     (limits-uniqueness-r-p r-type x)
     (let ((zero (limits-uniqueness-zero r-type))
           (one (limits-uniqueness-one r-type)))
       (and
        (equal (limits-uniqueness-add r-type x zero) x)
        (equal
         (limits-uniqueness-add
          r-type x (limits-uniqueness-opp r-type x))
         zero)
        (equal (limits-uniqueness-mul r-type x one) x)
        (limits-uniqueness-le r-type x x)
        (limits-uniqueness-le
         r-type zero (limits-uniqueness-abs r-type x))
        (equal
         (limits-uniqueness-abs
          r-type (limits-uniqueness-opp r-type x))
         (limits-uniqueness-abs r-type x)))))))

(defun-sk limits-uniqueness-binary-laws-p (r-type)
  (forall (x y)
    (implies
     (and
      (limits-uniqueness-r-p r-type x)
      (limits-uniqueness-r-p r-type y))
     (and
      (equal
       (limits-uniqueness-add r-type x y)
       (limits-uniqueness-add r-type y x))
      (equal
       (limits-uniqueness-opp
        r-type (limits-uniqueness-add r-type x y))
       (limits-uniqueness-add
        r-type
        (limits-uniqueness-opp r-type x)
        (limits-uniqueness-opp r-type y)))
      (equal
       (limits-uniqueness-mul r-type x y)
       (limits-uniqueness-mul r-type y x))
      (limits-uniqueness-le
       r-type
       (limits-uniqueness-abs
        r-type (limits-uniqueness-add r-type x y))
       (limits-uniqueness-add
        r-type
        (limits-uniqueness-abs r-type x)
        (limits-uniqueness-abs r-type y)))
      (equal
       (limits-uniqueness-abs
        r-type (limits-uniqueness-sub r-type x y))
       (limits-uniqueness-abs
        r-type (limits-uniqueness-sub r-type y x)))
      (implies
       (equal
        (limits-uniqueness-sub r-type x y)
        (limits-uniqueness-zero r-type))
       (equal x y))))))

(defun-sk limits-uniqueness-ternary-laws-p (r-type)
  (forall (x y z)
    (implies
     (and
      (limits-uniqueness-r-p r-type x)
      (limits-uniqueness-r-p r-type y)
      (limits-uniqueness-r-p r-type z))
     (and
      (equal
       (limits-uniqueness-add
        r-type (limits-uniqueness-add r-type x y) z)
       (limits-uniqueness-add
        r-type x (limits-uniqueness-add r-type y z)))
      (equal
       (limits-uniqueness-mul
        r-type (limits-uniqueness-mul r-type x y) z)
       (limits-uniqueness-mul
        r-type x (limits-uniqueness-mul r-type y z)))
      (implies
       (and
        (limits-uniqueness-le r-type x y)
        (limits-uniqueness-le r-type y z))
       (limits-uniqueness-le r-type x z))
      (equal
       (limits-uniqueness-sub r-type x z)
       (limits-uniqueness-add
        r-type
        (limits-uniqueness-sub r-type x y)
        (limits-uniqueness-sub r-type y z)))))))

(defun-sk limits-uniqueness-add-monotone-p (r-type)
  (forall (a b c d)
    (implies
     (and
      (limits-uniqueness-r-p r-type a)
      (limits-uniqueness-r-p r-type b)
      (limits-uniqueness-r-p r-type c)
      (limits-uniqueness-r-p r-type d)
      (limits-uniqueness-le r-type a b)
      (limits-uniqueness-le r-type c d))
     (limits-uniqueness-le
      r-type
      (limits-uniqueness-add r-type a c)
      (limits-uniqueness-add r-type b d)))))

(defun-sk limits-uniqueness-small-for-all-positive-eps-p
    (r-type x)
  (forall (eps)
    (implies
     (and
      (limits-uniqueness-r-p r-type eps)
      (limits-uniqueness-lt
       r-type (limits-uniqueness-zero r-type) eps))
     (limits-uniqueness-le
      r-type
      (limits-uniqueness-abs r-type x)
      (limits-uniqueness-add r-type eps eps)))))

(defun-sk limits-uniqueness-epsilon-separation-p (r-type)
  (forall (x)
    (implies
     (and
      (limits-uniqueness-r-p r-type x)
      (limits-uniqueness-small-for-all-positive-eps-p
       r-type x))
     (equal x (limits-uniqueness-zero r-type)))))

(defun limits-uniqueness-structure-p (r-type n-type)
  (and
   (limits-uniqueness-r-p
    r-type (limits-uniqueness-zero r-type))
   (limits-uniqueness-r-p
    r-type (limits-uniqueness-one r-type))
   (limits-uniqueness-operation-closure-p r-type n-type)
   (limits-uniqueness-directed-p n-type)
   (limits-uniqueness-unary-laws-p r-type)
   (limits-uniqueness-binary-laws-p r-type)
   (limits-uniqueness-ternary-laws-p r-type)
   (limits-uniqueness-add-monotone-p r-type)
   (limits-uniqueness-epsilon-separation-p r-type)))

(defun-sk limits-uniqueness-abs-sub-triangle-statement ()
  (forall (r-type n-type x y z)
    (implies
     (and
      (limits-uniqueness-structure-p r-type n-type)
      (limits-uniqueness-r-p r-type x)
      (limits-uniqueness-r-p r-type y)
      (limits-uniqueness-r-p r-type z))
     (limits-uniqueness-le
      r-type
      (limits-uniqueness-abs
       r-type (limits-uniqueness-sub r-type x z))
      (limits-uniqueness-add
       r-type
       (limits-uniqueness-abs
        r-type (limits-uniqueness-sub r-type x y))
       (limits-uniqueness-abs
        r-type (limits-uniqueness-sub r-type y z)))))))

(defun-sk limits-uniqueness-eventually-p
    (r-type n-type sequence limit-value eps threshold)
  (forall (n)
    (implies
     (and
      (limits-uniqueness-n-p n-type n)
      (limits-uniqueness-nle n-type threshold n))
     (limits-uniqueness-le
      r-type
      (limits-uniqueness-abs
       r-type
       (limits-uniqueness-sub
        r-type
        (limits-uniqueness-sequence-value
         r-type n-type sequence n)
        limit-value))
      eps))))

(defun-sk limits-uniqueness-threshold-exists-p
    (r-type n-type sequence limit-value eps)
  (exists (threshold)
    (and
     (limits-uniqueness-n-p n-type threshold)
     (limits-uniqueness-eventually-p
      r-type n-type sequence limit-value eps threshold))))

(defun-sk limits-uniqueness-limit-p
    (r-type n-type sequence limit-value)
  (forall (eps)
    (implies
     (and
      (limits-uniqueness-r-p r-type eps)
      (limits-uniqueness-lt
       r-type (limits-uniqueness-zero r-type) eps))
     (limits-uniqueness-threshold-exists-p
      r-type n-type sequence limit-value eps))))

(defun-sk limits-uniqueness-statement ()
  (forall (r-type n-type sequence l m)
    (implies
     (and
      (limits-uniqueness-structure-p r-type n-type)
      (limits-uniqueness-sequence-typed-p
       r-type n-type sequence)
      (limits-uniqueness-r-p r-type l)
      (limits-uniqueness-r-p r-type m)
      (limits-uniqueness-limit-p
       r-type n-type sequence l)
      (limits-uniqueness-limit-p
       r-type n-type sequence m))
     (equal l m))))

(value-triple :itpeval-statement-checked)
:q
