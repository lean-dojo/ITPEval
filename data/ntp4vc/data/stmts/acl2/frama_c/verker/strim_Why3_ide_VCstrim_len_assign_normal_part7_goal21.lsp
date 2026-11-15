;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strim_Why3_ide_VCstrim_len_assign_normal_part7_goal21:
;; a strim verification condition asserting inclusion of the byte after the
;; current address in the original string region, under the stated string,
;; memory-validity, address-order, whitespace, and no-null-prefix hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sln21-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sln21-address-base (address)
  (car address))

(defun sln21-address-offset (address)
  (cdr address))

(defun sln21-shift (address amount)
  (cons
   (sln21-address-base address)
   (+ (sln21-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary source
;; functions t_1 and t, together with region, address order, logical
;; strlen, unsigned conversion, linkedness, and constancy.

(defstub sln21-memory-1 (address) t)
(defstub sln21-allocation (index) t)
(defstub sln21-region (base) t)
(defstub sln21-addr-le-op (left right) t)
(defstub sln21-addr-lt-op (left right) t)
(defstub sln21-l-strlen (address) t)
(defstub sln21-to-uint64 (value) t)
(defstub sln21-linked-op () t)
(defstub sln21-sconst-op () t)

;; Preserve all source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk sln21-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (sln21-address-p address)
      (and
       (integerp
        (sln21-memory-1 address))
       (integerp
        (sln21-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (sln21-allocation index)))
     (implies
      (integerp base)
      (integerp
       (sln21-region base)))
     (implies
      (integerp value)
      (integerp
       (sln21-to-uint64 value))))))

(defun sln21-addr-le-p (left right)
  (if (sln21-addr-le-op left right) t nil))

(defun sln21-addr-lt-p (left right)
  (if (sln21-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source relations are exactly integer
;; order on offsets.

(defun-sk sln21-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (sln21-address-p left)
      (sln21-address-p right)
      (equal
       (sln21-address-base left)
       (sln21-address-base right)))
     (and
      (equal
       (sln21-addr-le-p left right)
       (<=
        (sln21-address-offset left)
        (sln21-address-offset right)))
      (equal
       (sln21-addr-lt-p left right)
       (<
        (sln21-address-offset left)
        (sln21-address-offset right)))))))

(defun sln21-linked-p ()
  (if (sln21-linked-op) t nil))

(defun sln21-sconst-p ()
  (if (sln21-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun sln21-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sln21-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Exact source definition of the C whitespace predicate.

(defun sln21-isspace-p (value)
  (or
   (equal value 9)
   (equal value 10)
   (equal value 12)
   (equal value 13)
   (equal value 32)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation.

(defun-sk sln21-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sln21-is-uint64-p
       (sln21-to-uint64 value))
      (implies
       (sln21-is-uint64-p value)
       (equal
        (sln21-to-uint64 value)
        value))
      (equal
       (sln21-to-uint64
        (sln21-to-uint64 value))
       (sln21-to-uint64 value))))))

;; Exact unfoldings of Memory.valid_rw, Memory.invalid, and Memory.included.

(defun sln21-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (sln21-address-base address))
    (<= 0
        (sln21-address-offset address))
    (<=
     (+ (sln21-address-offset address)
        length)
     (sln21-allocation
      (sln21-address-base address))))))

(defun sln21-invalid-p (address length)
  (implies
   (< 0 length)
   (or
    (<=
     (sln21-allocation
      (sln21-address-base address))
     (sln21-address-offset address))
    (<=
     (+ (sln21-address-offset address)
        length)
     0))))

(defun sln21-included-p
    (left left-length right right-length)
  (implies
   (< 0 left-length)
   (and
    (<= 0 right-length)
    (equal
     (sln21-address-base left)
     (sln21-address-base right))
    (<=
     (sln21-address-offset right)
     (sln21-address-offset left))
    (<=
     (+ (sln21-address-offset left)
        left-length)
     (+ (sln21-address-offset right)
        right-length)))))

;; Exact unfolding of A_Strlen.p_valid_str. Its terminating index remains an
;; internal existential over all mathematical integers, and its character
;; condition remains universal over every mathematical-integer position.

(defun-sk sln21-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (sln21-is-sint8-p
       (sln21-memory-1
        (sln21-shift address position)))))))

(defun-sk sln21-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (sln21-memory-1
       (sln21-shift address index))
      0)
     (sln21-is-uint64-p index)
     (sln21-valid-rw-p
      (sln21-shift address 0)
      (+ 1 index))
     (sln21-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk sln21-strlen-laws-p ()
  (forall (address)
    (implies
     (sln21-address-p address)
     (and
      (if
          (equal
           (sln21-memory-1
            (sln21-shift address 0))
           0)
          (equal
           (sln21-l-strlen address)
           0)
        (equal
         (sln21-to-uint64
          (+ 1
             (sln21-l-strlen
              (sln21-shift address 1))))
         (sln21-l-strlen address)))
      (sln21-is-uint64-p
       (sln21-l-strlen address))))))

;; Preserve the source's two internal universal hypotheses without bounding
;; their integer or address domains.

(defun-sk sln21-no-null-before-p
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
         (sln21-memory-1
          (sln21-shift address position))
         0)))))))

(defun-sk sln21-intervening-addresses-space-p
    (lower upper)
  (forall (candidate)
    (implies
     (sln21-address-p candidate)
     (implies
      (sln21-addr-lt-p lower candidate)
      (implies
       (sln21-addr-le-p candidate upper)
       (sln21-isspace-p
        (sln21-memory-1 candidate)))))))

(defun-sk
    ntp4vc-strim-len-assign-normal-part7-goal21-statement ()
  (forall
   (p a a1)
   (implies
    (and
     (booleanp p)
     (sln21-address-p a)
     (sln21-address-p a1)
     (sln21-function-types-p)
     (sln21-address-order-laws-p)
     (sln21-to-uint64-laws-p)
     (sln21-strlen-laws-p))
    (let*
        ((x
          (sln21-l-strlen a))
         (a2
          (sln21-shift a (- x 1)))
         (x1
          (sln21-memory-1 a2))
         (x2
          (sln21-memory-1 a1))
         (a3
          (sln21-shift a -1))
         (a4
          (sln21-shift a1 1)))
      (implies
       (and
        (not (equal x 0))
        (equal
         (sln21-memory-1
          (sln21-shift a x))
         0)
        (not (equal x1 0))
        (< 0 x)
        (<=
         (sln21-region
          (sln21-address-base a))
         0)
        (sln21-linked-p)
        (sln21-sconst-p)
        (sln21-is-sint8-p x2)
        (sln21-valid-string-p a)
        (sln21-is-uint64-p x)
        (sln21-addr-le-p a3 a1)
        (not
         (sln21-invalid-p a4 1))
        (sln21-addr-le-p a1 a2)
        (sln21-is-sint8-p x1)
        (if
            (sln21-addr-le-p a a1)
            (and
             (equal p nil)
             (not
              (sln21-isspace-p x2)))
          (or
            (equal a3 a1)
            (not
             (sln21-isspace-p x2))))
        (sln21-no-null-before-p a x)
        (sln21-intervening-addresses-space-p
         a1 a2))
       (sln21-included-p
        a4
        1
        (sln21-shift a 0)
        (+ 1 x)))))))

(value-triple :itpeval-statement-checked)

:q
