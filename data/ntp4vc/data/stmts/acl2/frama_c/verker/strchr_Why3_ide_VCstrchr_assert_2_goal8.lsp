;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strchr_Why3_ide_VCstrchr_assert_2_goal8:
;; the endpoint of a valid C string is the current address exactly when the
;; searched signed byte is zero, under the stated strchr, address-order,
;; memory-validity, linkedness, constancy, and no-earlier-match hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun scg8-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun scg8-address-base (address)
  (car address))

(defun scg8-address-offset (address)
  (cdr address))

(defun scg8-shift (address amount)
  (cons
   (scg8-address-base address)
   (+ (scg8-address-offset address) amount)))

(defun scg8-null-address ()
  (cons 0 0))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strchr, C integer conversion,
;; linkedness, and constancy symbols.

(defstub scg8-character-memory (address) t)
(defstub scg8-allocation (index) t)
(defstub scg8-region (base) t)
(defstub scg8-addr-le-op (left right) t)
(defstub scg8-addr-lt-op (left right) t)
(defstub scg8-l-strlen (address) t)
(defstub scg8-l-strchr (address value) t)
(defstub scg8-to-uint8 (value) t)
(defstub scg8-to-sint8 (value) t)
(defstub scg8-to-uint64 (value) t)
(defstub scg8-to-sint64 (value) t)
(defstub scg8-linked-op () t)
(defstub scg8-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk scg8-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (scg8-address-p address)
      (and
       (integerp
        (scg8-character-memory address))
       (integerp
        (scg8-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (scg8-allocation index)))
     (implies
      (integerp base)
      (integerp
       (scg8-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (scg8-to-uint8 value))
       (integerp
        (scg8-to-sint8 value))
       (integerp
        (scg8-to-uint64 value))
       (integerp
        (scg8-to-sint64 value))))
     (implies
      (and
       (scg8-address-p address)
       (integerp value))
      (scg8-address-p
       (scg8-l-strchr address value))))))

(defun scg8-addr-le-p (left right)
  (if (scg8-addr-le-op left right) t nil))

(defun scg8-addr-lt-p (left right)
  (if (scg8-addr-lt-op left right) t nil))

;; Exact source laws for address order: on addresses with equal bases, addr_le
;; and addr_lt are precisely integer order on offsets.

(defun-sk scg8-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (scg8-address-p left)
      (scg8-address-p right)
      (equal
       (scg8-address-base left)
       (scg8-address-base right)))
     (and
      (equal
       (scg8-addr-le-p left right)
       (<=
        (scg8-address-offset left)
        (scg8-address-offset right)))
      (equal
       (scg8-addr-lt-p left right)
       (<
        (scg8-address-offset left)
        (scg8-address-offset right)))))))

(defun scg8-linked-p ()
  (if (scg8-linked-op) t nil))

(defun scg8-sconst-p ()
  (if (scg8-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun scg8-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun scg8-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun scg8-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun scg8-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun scg8-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint8 operation.

(defun-sk scg8-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg8-is-uint8-p
       (scg8-to-uint8 value))
      (implies
       (scg8-is-uint8-p value)
       (equal
        (scg8-to-uint8 value)
        value))
      (equal
       (scg8-to-uint8
        (scg8-to-uint8 value))
       (scg8-to-uint8 value))))))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_sint8 operation.

(defun-sk scg8-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg8-is-sint8-p
       (scg8-to-sint8 value))
      (implies
       (scg8-is-sint8-p value)
       (equal
        (scg8-to-sint8 value)
        value))
      (equal
       (scg8-to-sint8
        (scg8-to-sint8 value))
       (scg8-to-sint8 value))))))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation.

(defun-sk scg8-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg8-is-uint64-p
       (scg8-to-uint64 value))
      (implies
       (scg8-is-uint64-p value)
       (equal
        (scg8-to-uint64 value)
        value))
      (equal
       (scg8-to-uint64
        (scg8-to-uint64 value))
       (scg8-to-uint64 value))))))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_sint64 operation.

(defun-sk scg8-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg8-is-sint64-p
       (scg8-to-sint64 value))
      (implies
       (scg8-is-sint64-p value)
       (equal
        (scg8-to-sint64 value)
        value))
      (equal
       (scg8-to-sint64
        (scg8-to-sint64 value))
       (scg8-to-sint64 value))))))

;; Exact Cint.proj_int8 and Cint.proj_int64 interaction laws.

(defun-sk scg8-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (scg8-to-sint8
        (scg8-to-uint8 value))
       (scg8-to-sint8 value))
      (equal
       (scg8-to-sint64
        (scg8-to-uint64 value))
       (scg8-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun scg8-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (scg8-address-base address))
    (<= 0
        (scg8-address-offset address))
    (<=
     (+ (scg8-address-offset address)
        length)
     (scg8-allocation
      (scg8-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk scg8-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (scg8-is-sint8-p
       (scg8-character-memory
        (scg8-shift address position)))))))

(defun-sk scg8-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (scg8-character-memory
       (scg8-shift address index))
      0)
     (scg8-is-uint64-p index)
     (scg8-valid-rw-p
      (scg8-shift address 0)
      (+ 1 index))
     (scg8-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk scg8-strlen-laws-p ()
  (forall (address)
    (implies
     (scg8-address-p address)
     (and
      (if
          (equal
           (scg8-character-memory
            (scg8-shift address 0))
           0)
          (equal
           (scg8-l-strlen address)
           0)
        (equal
         (scg8-to-uint64
          (+ 1
             (scg8-l-strlen
              (scg8-shift address 1))))
         (scg8-l-strlen address)))
      (scg8-is-uint64-p
       (scg8-l-strlen address))))))

;; Exact universal closure of A_Strchr.fix_l_strchr.

(defun-sk scg8-strchr-law-p ()
  (forall (address value)
    (implies
     (and
      (scg8-address-p address)
      (integerp value))
     (if
         (equal
          (scg8-character-memory address)
          value)
         (equal
          (scg8-l-strchr address value)
          address)
       (if
           (equal
            (scg8-character-memory address)
            0)
           (equal
            (scg8-l-strchr address value)
            (scg8-null-address))
         (equal
          (scg8-l-strchr
           (scg8-shift address 1)
           value)
          (scg8-l-strchr address value)))))))

;; The final source hypothesis retains its universal quantifier over every
;; address rather than exposing a witness or restricting the carrier.

(defun-sk scg8-no-earlier-match-p
    (start current value)
  (forall (candidate)
    (implies
     (scg8-address-p candidate)
     (implies
      (scg8-addr-lt-p candidate current)
      (implies
       (scg8-addr-le-p start candidate)
       (not
        (equal
         value
         (scg8-character-memory candidate))))))))

(defun-sk ntp4vc-strchr-assert-2-goal8-statement ()
  (forall
   (a a1 i)
   (implies
    (and
     (scg8-address-p a)
     (scg8-address-p a1)
     (integerp i)
     (scg8-function-types-p)
     (scg8-address-order-laws-p)
     (scg8-to-uint8-laws-p)
     (scg8-to-sint8-laws-p)
     (scg8-to-uint64-laws-p)
     (scg8-to-sint64-laws-p)
     (scg8-signed-unsigned-projection-laws-p)
     (scg8-strlen-laws-p)
     (scg8-strchr-law-p))
    (let*
        ((x
          (scg8-character-memory a))
         (a2
          (scg8-shift
           a1
           (scg8-l-strlen a1))))
      (implies
       (and
        (equal
         x
         (scg8-to-sint8 i))
        (equal
         (scg8-l-strchr a1 x)
         (scg8-l-strchr a x))
        (equal
         (scg8-addr-lt-p a a2)
         (not (equal x 0)))
        (<=
         (scg8-region
          (scg8-address-base a1))
         0)
        (scg8-linked-p)
        (scg8-sconst-p)
        (scg8-is-sint32-p i)
        (scg8-addr-le-p a1 a)
        (scg8-is-sint8-p x)
        (scg8-valid-string-p a)
        (scg8-valid-string-p a1)
        (scg8-addr-le-p a a2)
        (scg8-no-earlier-match-p
         a1 a x))
       (equal
        (equal a2 a)
        (equal x 0)))))))

(value-triple :itpeval-statement-checked)

:q
