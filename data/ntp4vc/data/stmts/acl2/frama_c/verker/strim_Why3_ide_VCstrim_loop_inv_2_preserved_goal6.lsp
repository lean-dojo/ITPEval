;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strim_Why3_ide_VCstrim_loop_inv_2_preserved_goal6:
;; preservation of a strim loop invariant asserting that the character at a
;; constrained address is whitespace, under the stated string-validity,
;; address-order, byte-range, no-null-prefix, and intervening-space hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun slig6-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun slig6-address-base (address)
  (car address))

(defun slig6-address-offset (address)
  (cdr address))

(defun slig6-shift (address amount)
  (cons
   (slig6-address-base address)
   (+ (slig6-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary source
;; functions t_1 and t, together with region, address order, logical
;; strlen, unsigned conversion, linkedness, and constancy.

(defstub slig6-memory-1 (address) t)
(defstub slig6-allocation (index) t)
(defstub slig6-region (base) t)
(defstub slig6-addr-le-op (left right) t)
(defstub slig6-addr-lt-op (left right) t)
(defstub slig6-l-strlen (address) t)
(defstub slig6-to-uint64 (value) t)
(defstub slig6-linked-op () t)
(defstub slig6-sconst-op () t)

;; Preserve all source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk slig6-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (slig6-address-p address)
      (and
       (integerp
        (slig6-memory-1 address))
       (integerp
        (slig6-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (slig6-allocation index)))
     (implies
      (integerp base)
      (integerp
       (slig6-region base)))
     (implies
      (integerp value)
      (integerp
       (slig6-to-uint64 value))))))

(defun slig6-addr-le-p (left right)
  (if (slig6-addr-le-op left right) t nil))

(defun slig6-addr-lt-p (left right)
  (if (slig6-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source relations are exactly integer
;; order on offsets.

(defun-sk slig6-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (slig6-address-p left)
      (slig6-address-p right)
      (equal
       (slig6-address-base left)
       (slig6-address-base right)))
     (and
      (equal
       (slig6-addr-le-p left right)
       (<=
        (slig6-address-offset left)
        (slig6-address-offset right)))
      (equal
       (slig6-addr-lt-p left right)
       (<
        (slig6-address-offset left)
        (slig6-address-offset right)))))))

(defun slig6-linked-p ()
  (if (slig6-linked-op) t nil))

(defun slig6-sconst-p ()
  (if (slig6-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun slig6-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun slig6-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun slig6-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Exact source definition of the C whitespace predicate.

(defun slig6-isspace-p (value)
  (or
   (equal value 9)
   (equal value 10)
   (equal value 12)
   (equal value 13)
   (equal value 32)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation.

(defun-sk slig6-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (slig6-is-uint64-p
       (slig6-to-uint64 value))
      (implies
       (slig6-is-uint64-p value)
       (equal
        (slig6-to-uint64 value)
        value))
      (equal
       (slig6-to-uint64
        (slig6-to-uint64 value))
       (slig6-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun slig6-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (slig6-address-base address))
    (<= 0
        (slig6-address-offset address))
    (<=
     (+ (slig6-address-offset address)
        length)
     (slig6-allocation
      (slig6-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. Its terminating index remains an
;; internal existential over all mathematical integers, and its character
;; condition remains universal over every mathematical-integer position.

(defun-sk slig6-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (slig6-is-sint8-p
       (slig6-memory-1
        (slig6-shift address position)))))))

(defun-sk slig6-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (slig6-memory-1
       (slig6-shift address index))
      0)
     (slig6-is-uint64-p index)
     (slig6-valid-rw-p
      (slig6-shift address 0)
      (+ 1 index))
     (slig6-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk slig6-strlen-laws-p ()
  (forall (address)
    (implies
     (slig6-address-p address)
     (and
      (if
          (equal
           (slig6-memory-1
            (slig6-shift address 0))
           0)
          (equal
           (slig6-l-strlen address)
           0)
        (equal
         (slig6-to-uint64
          (+ 1
             (slig6-l-strlen
              (slig6-shift address 1))))
         (slig6-l-strlen address)))
      (slig6-is-uint64-p
       (slig6-l-strlen address))))))

;; Preserve the source's two internal universal hypotheses without bounding
;; their integer or address domains.

(defun-sk slig6-no-null-before-p
    (address length)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position length)
       (not
        (equal
         (slig6-memory-1
          (slig6-shift address position))
         0)))))))

(defun-sk slig6-intervening-addresses-space-p
    (lower upper)
  (forall (candidate)
    (implies
     (slig6-address-p candidate)
     (implies
      (slig6-addr-lt-p lower candidate)
      (implies
       (slig6-addr-le-p candidate upper)
       (slig6-isspace-p
        (slig6-memory-1 candidate)))))))

(defun-sk
    ntp4vc-strim-loop-inv-2-preserved-goal6-statement ()
  (forall
   (a a1 i a2)
   (implies
    (and
     (slig6-address-p a)
     (slig6-address-p a1)
     (integerp i)
     (slig6-address-p a2)
     (slig6-function-types-p)
     (slig6-address-order-laws-p)
     (slig6-to-uint64-laws-p)
     (slig6-strlen-laws-p))
    (let*
        ((x
          (slig6-l-strlen a))
         (a3
          (slig6-shift a (- x 1)))
         (x1
          (slig6-memory-1 a3))
         (x2
          (slig6-memory-1 a1)))
      (implies
       (and
        (not (equal i 0))
        (not (equal x 0))
        (equal
         (slig6-memory-1
          (slig6-shift a x))
         0)
        (not (equal x1 0))
        (< 0 x)
        (<=
         (slig6-region
          (slig6-address-base a))
         0)
        (slig6-linked-p)
        (slig6-sconst-p)
        (slig6-is-uint8-p i)
        (slig6-addr-le-p a a1)
        (slig6-is-sint8-p x2)
        (slig6-isspace-p x2)
        (slig6-valid-string-p a)
        (slig6-is-uint64-p x)
        (slig6-addr-lt-p
         (slig6-shift a1 -1)
         a2)
        (slig6-addr-le-p
         (slig6-shift a -1)
         a1)
        (slig6-addr-le-p a1 a3)
        (slig6-addr-le-p a2 a3)
        (slig6-is-sint8-p x1)
        (slig6-no-null-before-p a x)
       (slig6-intervening-addresses-space-p
         a1 a3))
       (slig6-isspace-p
        (slig6-memory-1 a2)))))))

(value-triple :itpeval-statement-checked)

:q
