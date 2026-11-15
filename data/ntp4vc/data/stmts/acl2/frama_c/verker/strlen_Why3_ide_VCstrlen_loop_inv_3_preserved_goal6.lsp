;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strlen_Why3_ide_VCstrlen_loop_inv_3_preserved_goal6:
;; preservation of the strlen loop length-offset equation after advancing the
;; current address by one, under the stated region, linkedness, constancy,
;; address-order, character-range, and valid-string hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun slg6-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun slg6-address-base (address)
  (car address))

(defun slg6-address-offset (address)
  (cdr address))

(defun slg6-shift (address amount)
  (cons
   (slg6-address-base address)
   (+ (slg6-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region,
;; address-order, logical strlen, unsigned conversion, linkedness, and
;; constancy symbols.

(defstub slg6-character-memory (address) t)
(defstub slg6-allocation (index) t)
(defstub slg6-region (base) t)
(defstub slg6-addr-le-op (left right) t)
(defstub slg6-l-strlen (address) t)
(defstub slg6-to-uint64 (value) t)
(defstub slg6-linked-op () t)
(defstub slg6-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk slg6-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (slg6-address-p address)
      (and
       (integerp
        (slg6-character-memory address))
       (integerp
        (slg6-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (slg6-allocation index)))
     (implies
      (integerp base)
      (integerp
       (slg6-region base)))
     (implies
      (integerp value)
      (integerp
       (slg6-to-uint64 value))))))

(defun slg6-addr-le-p (left right)
  (if (slg6-addr-le-op left right) t nil))

;; On addresses with equal bases, the source address relation is exactly
;; mathematical-integer order on offsets.

(defun-sk slg6-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (slg6-address-p left)
      (slg6-address-p right)
      (equal
       (slg6-address-base left)
       (slg6-address-base right)))
     (equal
      (slg6-addr-le-p left right)
      (<=
       (slg6-address-offset left)
       (slg6-address-offset right))))))

(defun slg6-linked-p ()
  (if (slg6-linked-op) t nil))

(defun slg6-sconst-p ()
  (if (slg6-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun slg6-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun slg6-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation.

(defun-sk slg6-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (slg6-is-uint64-p
       (slg6-to-uint64 value))
      (implies
       (slg6-is-uint64-p value)
       (equal
        (slg6-to-uint64 value)
        value))
      (equal
       (slg6-to-uint64
        (slg6-to-uint64 value))
       (slg6-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun slg6-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (slg6-address-base address))
    (<= 0
        (slg6-address-offset address))
    (<=
     (+ (slg6-address-offset address)
        length)
     (slg6-allocation
      (slg6-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk slg6-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (slg6-is-sint8-p
       (slg6-character-memory
        (slg6-shift address position)))))))

(defun-sk slg6-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (slg6-character-memory
       (slg6-shift address index))
      0)
     (slg6-is-uint64-p index)
     (slg6-valid-rw-p
      (slg6-shift address 0)
      (+ 1 index))
     (slg6-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk slg6-strlen-laws-p ()
  (forall (address)
    (implies
     (slg6-address-p address)
     (and
      (if
          (equal
           (slg6-character-memory
            (slg6-shift address 0))
           0)
          (equal
           (slg6-l-strlen address)
           0)
        (equal
         (slg6-to-uint64
          (+ 1
             (slg6-l-strlen
              (slg6-shift address 1))))
         (slg6-l-strlen address)))
      (slg6-is-uint64-p
       (slg6-l-strlen address))))))

(defun-sk
    ntp4vc-strlen-loop-inv-3-preserved-goal6-statement ()
  (forall
   (a a1)
   (implies
    (and
     (slg6-address-p a)
     (slg6-address-p a1)
     (slg6-function-types-p)
     (slg6-address-order-law-p)
     (slg6-to-uint64-laws-p)
     (slg6-strlen-laws-p))
    (let*
        ((x
          (slg6-character-memory a))
         (x1
          (slg6-l-strlen a1))
         (x2
          (+ (slg6-address-offset a1)
             x1))
         (x3
          (slg6-address-offset a)))
      (implies
       (and
        (not (equal x 0))
        (equal
         x2
         (+ x3
            (slg6-l-strlen a)))
        (<=
         (slg6-region
          (slg6-address-base a1))
         0)
        (slg6-linked-p)
        (slg6-sconst-p)
        (slg6-addr-le-p a1 a)
        (slg6-is-sint8-p x)
        (slg6-valid-string-p a)
        (slg6-valid-string-p a1)
        (slg6-addr-le-p
         a
         (slg6-shift a1 x1)))
       (equal
        (+ 1
           x3
           (slg6-l-strlen
            (slg6-shift a 1)))
        x2))))))

(value-triple :itpeval-statement-checked)

:q
