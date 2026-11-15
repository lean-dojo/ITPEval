;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/binary_search/binary_search_Why3_ide_VCbinary_search_post_result_goal0:
;; equivalence between a binary-search result flag and existence of the
;; searched integer in a sorted memory range, under the stated bounds and
;; readability conditions. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun bs0-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun bs0-address-base (address)
  (car address))

(defun bs0-address-offset (address)
  (cdr address))

(defun bs0-shift (address amount)
  (cons
   (bs0-address-base address)
   (+ (bs0-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t_1, allocation map t, region function, and linked
;; predicate specialized to t.

(defstub bs0-integer-memory (address) t)
(defstub bs0-allocation (index) t)
(defstub bs0-region (base) t)
(defstub bs0-linked-op () t)

(defun-sk bs0-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (bs0-address-p address)
      (integerp (bs0-integer-memory address)))
     (implies
      (integerp index)
      (integerp (bs0-allocation index)))
     (implies
      (integerp base)
      (integerp (bs0-region base))))))

(defun bs0-linked-p ()
  (if (bs0-linked-op) t nil))

(defun bs0-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun bs0-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfolding of Memory.valid_rd for the arbitrary allocation map t.

(defun bs0-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (bs0-address-base address)))
    (<= 0 (bs0-address-offset address))
    (<=
     (+ (bs0-address-offset address) length)
     (bs0-allocation (bs0-address-base address))))))

;; Exact unfoldings of the three source range predicates over all
;; mathematical integer indices.

(defun-sk bs0-sorted-range-p (a lower upper)
  (forall (left right)
    (implies
     (and
      (integerp left)
      (integerp right)
      (< right upper)
      (<= lower left)
      (< left right))
     (<=
      (bs0-integer-memory (bs0-shift a left))
      (bs0-integer-memory (bs0-shift a right))))))

(defun-sk bs0-lower-bound-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      value
      (bs0-integer-memory (bs0-shift a index))))))

(defun-sk bs0-strict-upper-bound-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<
      (bs0-integer-memory (bs0-shift a index))
      value))))

;; The source conclusion keeps the matching array index existentially
;; quantified.

(defun-sk bs0-value-occurs-p (a upper value)
  (exists (index)
    (and
     (integerp index)
     (equal
      (bs0-integer-memory (bs0-shift a index))
      value)
     (<= 0 index)
     (< index upper))))

(defun-sk ntp4vc-binary-search-post-result-goal0-statement ()
  (forall
   (a i2 i1 i i3)
   (implies
    (and
     (bs0-function-types-p)
     (bs0-address-p a)
     (integerp i2)
     (integerp i1)
     (integerp i)
     (integerp i3))
    (let*
        ((a1 (bs0-shift a i2))
         (x (bs0-integer-memory a1)))
      (implies
       (and
        (<= i2 i1)
        (<= 0 i2)
        (<= (bs0-region (bs0-address-base a)) 0)
        (bs0-linked-p)
        (bs0-is-uint32-p i1)
        (bs0-is-uint32-p i2)
        (bs0-is-sint32-p i)
        (bs0-is-sint32-p i3)
        (bs0-sorted-range-p a 0 i1)
        (bs0-is-sint32-p x)
        (bs0-lower-bound-p a i2 i1 i)
        (bs0-strict-upper-bound-p a 0 i2 i)
        (bs0-valid-rd-p (bs0-shift a 0) i1)
        (if (< i2 i1)
            (and
             (bs0-valid-rd-p a1 1)
             (if (<= x i)
                 (equal i3 1)
               (equal i3 0)))
          (equal i3 0)))
       (iff
        (bs0-value-occurs-p a i1 i)
        (not (equal i3 0))))))))

(value-triple :itpeval-statement-checked)

:q
