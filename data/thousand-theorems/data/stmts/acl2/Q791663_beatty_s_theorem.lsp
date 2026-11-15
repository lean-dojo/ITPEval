;; Statement-only formalization of thousand-theorems corpus artifact Q791663,
;; "Beatty's theorem": Holder-conjugate real slopes give complementary integer
;; Beatty sets, and irrational conjugate slopes partition the positive integers
;; by their positive-index Beatty sequences. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces present an arbitrary Archimedean ordered
;; field through its integer embedding and floor operation. Every such
;; presentation embeds into the real field, while the real field itself is one
;; such presentation. Integer indices and set membership witnesses are
;; quantified internally and are not represented by finite tables.

(defstub q791663-member-p (real-type value) t)
(defstub q791663-zero (real-type) t)
(defstub q791663-one (real-type) t)
(defstub q791663-add (real-type left right) t)
(defstub q791663-multiply (real-type left right) t)
(defstub q791663-negate (real-type value) t)
(defstub q791663-inverse (real-type value) t)
(defstub q791663-less (real-type left right) t)
(defstub q791663-integer-embedding (real-type integer) t)
(defstub q791663-floor (real-type value) t)

(defun q791663-leq (real-type left right)
  (not (q791663-less real-type right left)))

(defun q791663-r-add (real-type left right)
  (q791663-add real-type left right))

(defun q791663-r-multiply (real-type left right)
  (q791663-multiply real-type left right))

(defun q791663-r-negate (real-type value)
  (q791663-negate real-type value))

(defun q791663-r-inverse (real-type value)
  (q791663-inverse real-type value))

(defun-sk q791663-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (q791663-member-p real-type x)
      (q791663-member-p real-type y)
      (q791663-member-p real-type z))
     (let* ((zero (q791663-zero real-type))
            (one (q791663-one real-type))
            (xy-add (q791663-r-add real-type x y))
            (yz-add (q791663-r-add real-type y z))
            (xy-mul (q791663-r-multiply real-type x y))
            (yz-mul (q791663-r-multiply real-type y z))
            (neg-x (q791663-r-negate real-type x))
            (inv-x (q791663-r-inverse real-type x)))
       (and
        (q791663-member-p real-type xy-add)
        (q791663-member-p real-type xy-mul)
        (q791663-member-p real-type neg-x)
        (q791663-member-p real-type inv-x)
        (equal
         (q791663-r-add real-type xy-add z)
         (q791663-r-add real-type x yz-add))
        (equal xy-add (q791663-r-add real-type y x))
        (equal (q791663-r-add real-type x zero) x)
        (equal (q791663-r-add real-type x neg-x) zero)
        (equal
         (q791663-r-multiply real-type xy-mul z)
         (q791663-r-multiply real-type x yz-mul))
        (equal xy-mul (q791663-r-multiply real-type y x))
        (equal (q791663-r-multiply real-type x one) x)
        (implies
         (equal x zero)
         (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal
          (q791663-r-multiply real-type x inv-x)
          one))
        (equal
         (q791663-r-multiply real-type x yz-add)
         (q791663-r-add
          real-type
          (q791663-r-multiply real-type x y)
          (q791663-r-multiply real-type x z))))))))

(defun-sk q791663-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (q791663-member-p real-type x)
      (q791663-member-p real-type y)
      (q791663-member-p real-type z))
     (let ((zero (q791663-zero real-type)))
       (and
        (not (q791663-less real-type x x))
        (or
         (q791663-less real-type x y)
         (equal x y)
         (q791663-less real-type y x))
        (implies
         (and
          (q791663-less real-type x y)
          (q791663-less real-type y z))
         (q791663-less real-type x z))
        (implies
         (q791663-less real-type x y)
         (q791663-less
          real-type
          (q791663-r-add real-type x z)
          (q791663-r-add real-type y z)))
        (implies
         (and
          (q791663-less real-type zero x)
          (q791663-less real-type zero y))
         (q791663-less
          real-type
          zero
          (q791663-r-multiply real-type x y))))))))

(defun-sk q791663-integer-embedding-laws-p (real-type)
  (forall (m n)
    (implies
     (and (integerp m) (integerp n))
     (let ((embed-m
            (q791663-integer-embedding real-type m))
           (embed-n
            (q791663-integer-embedding real-type n)))
       (and
        (q791663-member-p real-type embed-m)
        (q791663-member-p real-type embed-n)
        (equal
         (q791663-integer-embedding real-type 0)
         (q791663-zero real-type))
        (equal
         (q791663-integer-embedding real-type 1)
         (q791663-one real-type))
        (equal
         (q791663-integer-embedding real-type (+ m n))
         (q791663-r-add real-type embed-m embed-n))
        (equal
         (q791663-integer-embedding real-type (* m n))
         (q791663-r-multiply real-type embed-m embed-n))
        (equal
         (q791663-integer-embedding real-type (- m))
         (q791663-r-negate real-type embed-m))
        (iff
         (< m n)
         (q791663-less real-type embed-m embed-n)))))))

(defun-sk q791663-floor-laws-p (real-type)
  (forall (x)
    (implies
     (q791663-member-p real-type x)
     (let* ((floor-x (q791663-floor real-type x))
            (embed-floor
             (q791663-integer-embedding real-type floor-x))
            (embed-next
             (q791663-integer-embedding real-type (+ floor-x 1))))
       (and
        (integerp floor-x)
        (q791663-leq real-type embed-floor x)
        (q791663-less real-type x embed-next))))))

(defun q791663-real-presentation-p (real-type)
  (let ((zero (q791663-zero real-type))
        (one (q791663-one real-type)))
    (and
     (q791663-member-p real-type zero)
     (q791663-member-p real-type one)
     (not (equal zero one))
     (q791663-less real-type zero one)
     (q791663-field-laws-p real-type)
     (q791663-order-laws-p real-type)
     (q791663-integer-embedding-laws-p real-type)
     (q791663-floor-laws-p real-type))))

;; Real.HolderConjugate r s: both slopes are positive and their reciprocals
;; sum to one.

(defun q791663-holder-conjugate-p (real-type r s)
  (let ((zero (q791663-zero real-type))
        (one (q791663-one real-type)))
    (and
     (q791663-member-p real-type r)
     (q791663-member-p real-type s)
     (q791663-less real-type zero r)
     (q791663-less real-type zero s)
     (equal
      (q791663-r-add
       real-type
       (q791663-r-inverse real-type r)
       (q791663-r-inverse real-type s))
      one))))

;; Irrationality is the absence of a ratio of embedded integers with nonzero
;; denominator.

(defun-sk q791663-irrational-p (real-type r)
  (forall (numerator denominator)
    (implies
     (and
      (integerp numerator)
      (integerp denominator)
      (not (equal denominator 0)))
     (not
      (equal
       (q791663-r-multiply
        real-type
        r
        (q791663-integer-embedding real-type denominator))
       (q791663-integer-embedding real-type numerator))))))

;; Membership in B_r = {floor(k*r) | k is an integer}.

(defun-sk q791663-beatty-member-p (real-type r j)
  (exists (k)
    (and
     (integerp j)
     (integerp k)
     (equal
      (q791663-floor
       real-type
       (q791663-r-multiply
        real-type
        (q791663-integer-embedding real-type k)
        r))
      j))))

;; Membership in B'_r = {ceil(k*r)-1 | k is an integer}, using
;; ceil(x) = -floor(-x).

(defun-sk q791663-beatty-prime-member-p (real-type r j)
  (exists (k)
    (and
     (integerp j)
     (integerp k)
     (equal
      (-
       (-
        (q791663-floor
         real-type
         (q791663-r-negate
          real-type
          (q791663-r-multiply
           real-type
           (q791663-integer-embedding real-type k)
           r))))
       1)
      j))))

;; Membership in B+_r = {floor(k*r) | k is a positive integer}.

(defun-sk q791663-positive-beatty-member-p (real-type r j)
  (exists (k)
    (and
     (integerp j)
     (integerp k)
     (< 0 k)
     (equal
      (q791663-floor
       real-type
       (q791663-r-multiply
        real-type
        (q791663-integer-embedding real-type k)
        r))
      j))))

;; compl_beattySeq: the complement of B_r in the integers is B'_s.

(defun-sk q791663-compl-beatty-seq-conclusion-p
    (real-type r s)
  (forall (j)
    (implies
     (integerp j)
     (iff
      (not (q791663-beatty-member-p real-type r j))
      (q791663-beatty-prime-member-p real-type s j)))))

;; Irrational.beattySeq_symmDiff_beattySeq_pos: the symmetric difference of
;; B+_r and B+_s is exactly the set of positive integers.

(defun-sk q791663-positive-partition-conclusion-p
    (real-type r s)
  (forall (j)
    (implies
     (integerp j)
     (iff
      (if (q791663-positive-beatty-member-p real-type r j)
          (not
           (q791663-positive-beatty-member-p real-type s j))
        (q791663-positive-beatty-member-p real-type s j))
      (< 0 j)))))

(defun thousand-theorems-q791663-compl-beatty-seq-statement
    (real-type r s)
  (implies
   (and
    (q791663-real-presentation-p real-type)
    (q791663-holder-conjugate-p real-type r s))
   (q791663-compl-beatty-seq-conclusion-p
    real-type r s)))

(defun thousand-theorems-q791663-beatty-s-theorem-statement
    (real-type r s)
  (implies
   (and
    (q791663-real-presentation-p real-type)
    (q791663-holder-conjugate-p real-type r s)
    (q791663-irrational-p real-type r))
   (q791663-positive-partition-conclusion-p
    real-type r s)))

(value-triple :itpeval-statement-checked)
:q
