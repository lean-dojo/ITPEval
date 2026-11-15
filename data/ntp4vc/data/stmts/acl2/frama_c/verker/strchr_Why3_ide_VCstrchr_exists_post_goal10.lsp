;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strchr_Why3_ide_VCstrchr_exists_post_goal10:
;; the candidate address lies between the string start and its logical
;; endpoint under the stated strchr, address-order, valid-string, signed-byte,
;; linkedness, constancy, conditional-address, and no-earlier-match hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun scg10-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun scg10-address-base (address)
  (car address))

(defun scg10-address-offset (address)
  (cdr address))

(defun scg10-shift (address amount)
  (cons
   (scg10-address-base address)
   (+ (scg10-address-offset address) amount)))

(defun scg10-null-address ()
  (cons 0 0))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source's region,
;; address-order, logical strlen, logical strchr, C integer conversion,
;; linkedness, and constancy symbols.

(defstub scg10-character-memory (address) t)
(defstub scg10-allocation (index) t)
(defstub scg10-region (base) t)
(defstub scg10-addr-le-op (left right) t)
(defstub scg10-addr-lt-op (left right) t)
(defstub scg10-l-strlen (address) t)
(defstub scg10-l-strchr (address value) t)
(defstub scg10-to-uint8 (value) t)
(defstub scg10-to-sint8 (value) t)
(defstub scg10-to-uint64 (value) t)
(defstub scg10-to-sint64 (value) t)
(defstub scg10-linked-op () t)
(defstub scg10-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk scg10-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (scg10-address-p address)
      (and
       (integerp
        (scg10-character-memory address))
       (integerp
        (scg10-l-strlen address))))
     (implies
      (integerp index)
      (integerp
       (scg10-allocation index)))
     (implies
      (integerp base)
      (integerp
       (scg10-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (scg10-to-uint8 value))
       (integerp
        (scg10-to-sint8 value))
       (integerp
        (scg10-to-uint64 value))
       (integerp
        (scg10-to-sint64 value))))
     (implies
      (and
       (scg10-address-p address)
       (integerp value))
      (scg10-address-p
       (scg10-l-strchr address value))))))

(defun scg10-addr-le-p (left right)
  (if (scg10-addr-le-op left right) t nil))

(defun scg10-addr-lt-p (left right)
  (if (scg10-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; integer order on offsets.

(defun-sk scg10-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (scg10-address-p left)
      (scg10-address-p right)
      (equal
       (scg10-address-base left)
       (scg10-address-base right)))
     (and
      (equal
       (scg10-addr-le-p left right)
       (<=
        (scg10-address-offset left)
        (scg10-address-offset right)))
      (equal
       (scg10-addr-lt-p left right)
       (<
        (scg10-address-offset left)
        (scg10-address-offset right)))))))

(defun scg10-linked-p ()
  (if (scg10-linked-op) t nil))

(defun scg10-sconst-p ()
  (if (scg10-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun scg10-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun scg10-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun scg10-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

(defun scg10-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun scg10-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by the VC and its logical string recurrences.

(defun-sk scg10-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg10-is-uint8-p
       (scg10-to-uint8 value))
      (implies
       (scg10-is-uint8-p value)
       (equal
        (scg10-to-uint8 value)
        value))
      (equal
       (scg10-to-uint8
        (scg10-to-uint8 value))
       (scg10-to-uint8 value))))))

(defun-sk scg10-to-sint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg10-is-sint8-p
       (scg10-to-sint8 value))
      (implies
       (scg10-is-sint8-p value)
       (equal
        (scg10-to-sint8 value)
        value))
      (equal
       (scg10-to-sint8
        (scg10-to-sint8 value))
       (scg10-to-sint8 value))))))

(defun-sk scg10-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg10-is-uint64-p
       (scg10-to-uint64 value))
      (implies
       (scg10-is-uint64-p value)
       (equal
        (scg10-to-uint64 value)
        value))
      (equal
       (scg10-to-uint64
        (scg10-to-uint64 value))
       (scg10-to-uint64 value))))))

(defun-sk scg10-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (scg10-is-sint64-p
       (scg10-to-sint64 value))
      (implies
       (scg10-is-sint64-p value)
       (equal
        (scg10-to-sint64 value)
        value))
      (equal
       (scg10-to-sint64
        (scg10-to-sint64 value))
       (scg10-to-sint64 value))))))

;; Exact Cint.proj_int8 and Cint.proj_int64 interaction laws.

(defun-sk scg10-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (scg10-to-sint8
        (scg10-to-uint8 value))
       (scg10-to-sint8 value))
      (equal
       (scg10-to-sint64
        (scg10-to-uint64 value))
       (scg10-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun scg10-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (scg10-address-base address))
    (<= 0
        (scg10-address-offset address))
    (<=
     (+ (scg10-address-offset address)
        length)
     (scg10-allocation
      (scg10-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. The terminating position remains
;; an internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk scg10-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (scg10-is-sint8-p
       (scg10-character-memory
        (scg10-shift address position)))))))

(defun-sk scg10-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (scg10-character-memory
       (scg10-shift address index))
      0)
     (scg10-is-uint64-p index)
     (scg10-valid-rw-p
      (scg10-shift address 0)
      (+ 1 index))
     (scg10-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk scg10-strlen-laws-p ()
  (forall (address)
    (implies
     (scg10-address-p address)
     (and
      (if
          (equal
           (scg10-character-memory
            (scg10-shift address 0))
           0)
          (equal
           (scg10-l-strlen address)
           0)
        (equal
         (scg10-to-uint64
          (+ 1
             (scg10-l-strlen
              (scg10-shift address 1))))
         (scg10-l-strlen address)))
      (scg10-is-uint64-p
       (scg10-l-strlen address))))))

;; Exact universal closure of A_Strchr.fix_l_strchr.

(defun-sk scg10-strchr-law-p ()
  (forall (address value)
    (implies
     (and
      (scg10-address-p address)
      (integerp value))
     (if
         (equal
          (scg10-character-memory address)
          value)
         (equal
          (scg10-l-strchr address value)
          address)
       (if
           (equal
            (scg10-character-memory address)
            0)
           (equal
            (scg10-l-strchr address value)
            (scg10-null-address))
         (equal
          (scg10-l-strchr
           (scg10-shift address 1)
           value)
          (scg10-l-strchr address value)))))))

;; The final source hypothesis retains its universal quantifier over every
;; address rather than exposing a witness or restricting the carrier.

(defun-sk scg10-no-earlier-match-p
    (start current value)
  (forall (candidate)
    (implies
     (scg10-address-p candidate)
     (implies
      (scg10-addr-lt-p candidate current)
      (implies
       (scg10-addr-le-p start candidate)
       (not
        (equal
         value
         (scg10-character-memory candidate))))))))

(defun-sk ntp4vc-strchr-exists-post-goal10-statement ()
  (forall
   (a3 a a1 a2 i)
   (implies
    (and
     (scg10-address-p a3)
     (scg10-address-p a)
     (scg10-address-p a1)
     (scg10-address-p a2)
     (integerp i)
     (scg10-function-types-p)
     (scg10-address-order-laws-p)
     (scg10-to-uint8-laws-p)
     (scg10-to-sint8-laws-p)
     (scg10-to-uint64-laws-p)
     (scg10-to-sint64-laws-p)
     (scg10-signed-unsigned-projection-laws-p)
     (scg10-strlen-laws-p)
     (scg10-strchr-law-p))
    (let*
        ((x
          (scg10-character-memory a3))
         (x1
          (scg10-character-memory a))
         (x2
          (scg10-character-memory a1))
         (a4
          (scg10-shift
           a2
           (scg10-l-strlen a2))))
      (implies
       (and
        (equal
         x
         (scg10-to-sint8 i))
        (equal
         (scg10-l-strchr a2 x)
         (scg10-l-strchr a1 x))
        (<=
         (scg10-region
          (scg10-address-base a2))
         0)
        (scg10-linked-p)
        (scg10-sconst-p)
        (scg10-is-sint32-p i)
        (scg10-addr-le-p a2 a1)
        (scg10-addr-le-p a2 a3)
        (scg10-is-sint8-p x1)
        (scg10-is-sint8-p x2)
        (scg10-valid-string-p a1)
        (scg10-valid-string-p a2)
        (scg10-addr-le-p a1 a4)
        (scg10-addr-le-p a3 a4)
        (if
            (equal x x2)
            (and
             (equal a1 a)
             (equal
              (equal a4 a)
              (equal x1 0))
             (equal
              (scg10-addr-lt-p a a4)
              (not (equal x1 0))))
          (and
           (equal
            (scg10-null-address)
            a)
           (equal x2 0)))
        (scg10-no-earlier-match-p
         a2 a1 x))
       (and
        (scg10-addr-le-p a2 a)
        (scg10-addr-le-p a a4)))))))

(value-triple :itpeval-statement-checked)

:q
