;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/replace_copy/replace_copy_Why3_ide_VCreplace_copy_post_replace_goal0:
;; preservation of the replace-copy postcondition when the havoced memory
;; range changes from i_2 to i_3, under the stated equal-bound, integer-range,
;; region, linkedness, memory-validity, separation, unchanged-range, and
;; prior replacement hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun rc0-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun rc0-address-base (address)
  (car address))

(defun rc0-address-offset (address)
  (cdr address))

(defun rc0-shift (address amount)
  (cons
   (rc0-address-base address)
   (+ (rc0-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary source memories
;; t_1 and t_2, allocation map t, region function, and linked predicate
;; specialized to t.

(defstub rc0-t1 (address) t)
(defstub rc0-t2 (address) t)
(defstub rc0-allocation (index) t)
(defstub rc0-region (base) t)
(defstub rc0-linked-op () t)

(defun-sk rc0-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (rc0-address-p address)
      (and
       (integerp (rc0-t1 address))
       (integerp (rc0-t2 address))))
     (implies
      (integerp index)
      (integerp (rc0-allocation index)))
     (implies
      (integerp base)
      (integerp (rc0-region base))))))

(defun rc0-linked-p ()
  (if (rc0-linked-op) t nil))

(defun rc0-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun rc0-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfoldings of Memory.valid_rd, Memory.valid_rw, and
;; Memory.separated.

(defun rc0-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (rc0-address-base address)))
    (<= 0 (rc0-address-offset address))
    (<=
     (+ (rc0-address-offset address) length)
     (rc0-allocation (rc0-address-base address))))))

(defun rc0-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (rc0-address-base address))
    (<= 0 (rc0-address-offset address))
    (<=
     (+ (rc0-address-offset address) length)
     (rc0-allocation (rc0-address-base address))))))

(defun rc0-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (rc0-address-base left)
     (rc0-address-base right)))
   (<=
    (+ (rc0-address-offset right) right-length)
    (rc0-address-offset left))
   (<=
    (+ (rc0-address-offset left) left-length)
    (rc0-address-offset right))))

;; Exact pointwise value of havoc t_1 t_2 (shift a 0) length, using the
;; source havoc_access equation.

(defun rc0-havoc-read (a length query)
  (if
      (rc0-separated-p
       query 1 (rc0-shift a 0) length)
      (rc0-t2 query)
    (rc0-t1 query)))

;; Exact unfoldings of Axiomatic.p_unchanged_1' and
;; Axiomatic.p_replace_1' over all mathematical integer indices.

(defun-sk rc0-unchanged-p
    (a1 a lower upper havoc-length)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (equal
      (rc0-t2 (rc0-shift a1 index))
      (rc0-havoc-read
       a havoc-length (rc0-shift a1 index))))))

(defun-sk rc0-replace-p
    (a1 a bound old-value new-value havoc-length)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index bound))
     (let
         ((source-value
           (rc0-t2 (rc0-shift a1 index)))
          (destination-value
           (rc0-havoc-read
            a havoc-length (rc0-shift a index))))
       (and
        (implies
         (equal source-value old-value)
         (equal destination-value new-value))
        (implies
         (not (equal source-value old-value))
         (equal destination-value source-value)))))))

(defun-sk
    ntp4vc-replace-copy-post-replace-goal0-statement
    ()
  (forall
   (a1 a i2 i3 i i1)
   (implies
    (and
     (rc0-address-p a1)
     (rc0-address-p a)
     (integerp i2)
     (integerp i3)
     (integerp i)
     (integerp i1)
     (rc0-function-types-p))
    (let
        ((a2 (rc0-shift a1 0))
         (a3 (rc0-shift a 0)))
      (implies
       (and
        (<= i3 i2)
        (<= 0 i3)
        (<= i2 i3)
        (<= (rc0-region (rc0-address-base a)) 0)
        (<= (rc0-region (rc0-address-base a1)) 0)
        (rc0-linked-p)
        (rc0-is-uint32-p i2)
        (rc0-is-uint32-p i3)
        (rc0-is-sint32-p i)
        (rc0-is-sint32-p i1)
        (rc0-valid-rd-p a2 i2)
        (rc0-valid-rw-p a3 i2)
        (rc0-separated-p a2 i2 a 1)
        (rc0-unchanged-p a1 a i3 i2 i2)
        (rc0-replace-p a1 a i3 i1 i i2))
       (rc0-replace-p a1 a i3 i1 i i3))))))

(value-triple :itpeval-statement-checked)

:q
