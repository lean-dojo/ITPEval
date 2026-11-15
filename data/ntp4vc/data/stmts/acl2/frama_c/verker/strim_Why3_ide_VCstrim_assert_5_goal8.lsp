;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strim_Why3_ide_VCstrim_assert_5_goal8:
;; a strim verification condition relating the logical string length, ordered
;; addresses around a non-null character, whitespace throughout an intervening
;; address interval, and the preceding or observed character. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun stg8-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun stg8-address-base (address)
  (car address))

(defun stg8-address-offset (address)
  (cdr address))

(defun stg8-shift (address amount)
  (cons
   (stg8-address-base address)
   (+ (stg8-address-offset address) amount)))

;; Conservative interfaces represent the universally arbitrary source
;; functions t_1 and t, together with region, address order,
;; logical strlen, unsigned conversion, linkedness, and constancy.

(defstub stg8-memory-1 (address) t)
(defstub stg8-allocation (index) t)
(defstub stg8-region (base) t)
(defstub stg8-addr-le-op (left right) t)
(defstub stg8-addr-lt-op (left right) t)
(defstub stg8-l-strlen (address) t)
(defstub stg8-to-uint64 (value) t)
(defstub stg8-linked-op () t)
(defstub stg8-sconst-op () t)

;; Preserve all source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk stg8-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (stg8-address-p address)
      (and
       (integerp
        (stg8-memory-1 address))
       (integerp
        (stg8-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (stg8-allocation index)))
     (implies
      (integerp base)
      (integerp
       (stg8-region base)))
     (implies
      (integerp value)
      (integerp
       (stg8-to-uint64 value))))))

(defun stg8-addr-le-p (left right)
  (if (stg8-addr-le-op left right) t nil))

(defun stg8-addr-lt-p (left right)
  (if (stg8-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source relations are exactly integer
;; order on offsets.

(defun-sk stg8-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (stg8-address-p left)
      (stg8-address-p right)
      (equal
       (stg8-address-base left)
       (stg8-address-base right)))
     (and
      (equal
       (stg8-addr-le-p left right)
       (<=
        (stg8-address-offset left)
        (stg8-address-offset right)))
      (equal
       (stg8-addr-lt-p left right)
       (<
        (stg8-address-offset left)
        (stg8-address-offset right)))))))

(defun stg8-linked-p ()
  (if (stg8-linked-op) t nil))

(defun stg8-sconst-p ()
  (if (stg8-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun stg8-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun stg8-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Exact source definition of the C whitespace predicate.

(defun stg8-isspace-p (value)
  (or
   (equal value 9)
   (equal value 10)
   (equal value 12)
   (equal value 13)
   (equal value 32)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation.

(defun-sk stg8-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (stg8-is-uint64-p
       (stg8-to-uint64 value))
      (implies
       (stg8-is-uint64-p value)
       (equal
        (stg8-to-uint64 value)
        value))
      (equal
       (stg8-to-uint64
        (stg8-to-uint64 value))
       (stg8-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun stg8-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (stg8-address-base address))
    (<= 0
        (stg8-address-offset address))
    (<=
     (+ (stg8-address-offset address)
        length)
     (stg8-allocation
      (stg8-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. Its terminating index remains an
;; internal existential over all mathematical integers, and its character
;; condition remains universal over every mathematical-integer position.

(defun-sk stg8-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (stg8-is-sint8-p
       (stg8-memory-1
        (stg8-shift address position)))))))

(defun-sk stg8-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (stg8-memory-1
       (stg8-shift address index))
      0)
     (stg8-is-uint64-p index)
     (stg8-valid-rw-p
      (stg8-shift address 0)
      (+ 1 index))
     (stg8-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk stg8-strlen-laws-p ()
  (forall (address)
    (implies
     (stg8-address-p address)
     (and
      (if
          (equal
           (stg8-memory-1
            (stg8-shift address 0))
           0)
          (equal
           (stg8-l-strlen address)
           0)
        (equal
         (stg8-to-uint64
          (+ 1
             (stg8-l-strlen
              (stg8-shift address 1))))
         (stg8-l-strlen address)))
      (stg8-is-uint64-p
       (stg8-l-strlen address))))))

;; Preserve the source's two internal universal hypotheses without bounding
;; their integer or address domains.

(defun-sk stg8-no-null-before-p
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
         (stg8-memory-1
          (stg8-shift address position))
         0)))))))

(defun-sk stg8-intervening-addresses-space-p
    (lower upper)
  (forall (candidate)
    (implies
     (stg8-address-p candidate)
     (implies
      (stg8-addr-lt-p lower candidate)
      (implies
       (stg8-addr-le-p candidate upper)
       (stg8-isspace-p
        (stg8-memory-1 candidate)))))))

(defun-sk ntp4vc-strim-assert-5-goal8-statement ()
  (forall
   (a a1)
   (implies
    (and
     (stg8-address-p a)
     (stg8-address-p a1)
     (stg8-function-types-p)
     (stg8-address-order-laws-p)
     (stg8-to-uint64-laws-p)
     (stg8-strlen-laws-p))
    (let*
        ((x
          (stg8-l-strlen a))
         (a2
          (stg8-shift a (- x 1)))
         (x1
          (stg8-memory-1 a2))
         (x2
          (stg8-memory-1 a1))
         (a3
          (stg8-shift a -1)))
      (implies
       (and
        (not (equal x 0))
        (equal
         (stg8-memory-1
          (stg8-shift a x))
         0)
        (not (equal x1 0))
        (< 0 x)
        (<=
         (stg8-region
          (stg8-address-base a))
         0)
        (stg8-linked-p)
        (stg8-sconst-p)
        (not
         (stg8-addr-le-p a a1))
        (stg8-is-sint8-p x2)
        (stg8-valid-string-p a)
        (stg8-is-uint64-p x)
        (stg8-addr-le-p a3 a1)
        (stg8-addr-le-p a1 a2)
        (stg8-is-sint8-p x1)
        (stg8-no-null-before-p a x)
        (stg8-intervening-addresses-space-p
         a1 a2))
       (or
        (equal a3 a1)
        (not
         (stg8-isspace-p x2))))))))

(value-triple :itpeval-statement-checked)

:q
