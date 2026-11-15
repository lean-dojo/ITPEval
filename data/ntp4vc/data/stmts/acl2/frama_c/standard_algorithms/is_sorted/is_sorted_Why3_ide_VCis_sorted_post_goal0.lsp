;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/is_sorted/is_sorted_Why3_ide_VCis_sorted_post_goal0:
;; equivalence between sortedness of the full integer-memory range and the
;; nonzero result flag, under the stated branch state, weak sortedness,
;; integer bounds, linkedness, and memory-readability hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun isp0-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun isp0-address-base (address)
  (car address))

(defun isp0-address-offset (address)
  (cdr address))

(defun isp0-shift (address amount)
  (cons
   (isp0-address-base address)
   (+ (isp0-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t_1, allocation map t, region function, and linked
;; predicate specialized to t.

(defstub isp0-integer-memory (address) t)
(defstub isp0-allocation (index) t)
(defstub isp0-region (base) t)
(defstub isp0-linked-op () t)

(defun-sk isp0-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (isp0-address-p address)
      (integerp (isp0-integer-memory address)))
     (implies
      (integerp index)
      (integerp (isp0-allocation index)))
     (implies
      (integerp base)
      (integerp (isp0-region base))))))

(defun isp0-linked-p ()
  (if (isp0-linked-op) t nil))

(defun isp0-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun isp0-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Cint.to_uint32 is the canonical residue in [0, 2^32).

(defun isp0-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

;; Exact unfolding of Memory.valid_rd for the arbitrary allocation map t.

(defun isp0-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (isp0-address-base address)))
    (<= 0 (isp0-address-offset address))
    (<=
     (+ (isp0-address-offset address) length)
     (isp0-allocation (isp0-address-base address))))))

;; Exact unfoldings of Axiomatic.p_weaklysorted_1' and
;; Axiomatic.p_sorted_1' over all mathematical integer indices.

(defun-sk isp0-weakly-sorted-p (a lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= (+ 2 index) upper))
     (<=
      (isp0-integer-memory (isp0-shift a index))
      (isp0-integer-memory (isp0-shift a (+ 1 index)))))))

(defun-sk isp0-sorted-p (a lower upper)
  (forall (left right)
    (implies
     (and
      (integerp left)
      (integerp right)
      (< right upper)
      (<= lower left)
      (< left right))
     (<=
      (isp0-integer-memory (isp0-shift a left))
      (isp0-integer-memory (isp0-shift a right))))))

(defun-sk ntp4vc-is-sorted-post-goal0-statement ()
  (forall
   (i2 a i i1 p)
   (implies
    (and
     (integerp i2)
     (isp0-address-p a)
     (integerp i)
     (integerp i1)
     (booleanp p)
     (isp0-function-types-p))
    (let*
        ((x (+ 1 i2))
         (a1 (isp0-shift a i2)))
      (implies
       (and
        (<= (isp0-region (isp0-address-base a)) 0)
        (isp0-linked-p)
        (isp0-is-uint32-p i)
        (isp0-is-uint32-p i2)
        (isp0-is-sint32-p i1)
        (isp0-valid-rd-p (isp0-shift a 0) i)
        (if
            (< 0 i)
            (and
             (equal p nil)
             (isp0-weakly-sorted-p a 0 x)
             (if
                 (<= (+ 2 i2) i)
                 (and
                  (equal i1 0)
                  (<
                   (isp0-integer-memory (isp0-shift a x))
                   (isp0-integer-memory a1))
                  (<= i2 4294967294)
                  (isp0-valid-rd-p a1 1)
                  (isp0-valid-rd-p
                   (isp0-shift a (isp0-to-uint32 x))
                   1))
               (equal i1 1)))
          (equal i1 1)))
       (iff
        (isp0-sorted-p a 0 i)
        (not (equal i1 0))))))))

(value-triple :itpeval-statement-checked)

:q
