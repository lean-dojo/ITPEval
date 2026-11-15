;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/klibc_string/strcasecmp_Why3_ide_VCstrcasecmp_not_eq_post_part2_goal19:
;; failure of universal equality between uppercased bytes of two string
;; prefixes, under the stated address, string-length, memory-separation,
;; character-conversion, linkedness, and constancy hypotheses. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sc19-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sc19-address-base (address)
  (car address))

(defun sc19-address-offset (address)
  (cdr address))

(defun sc19-shift (address amount)
  (cons
   (sc19-address-base address)
   (+ (sc19-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; character memory t_1, allocation map t, region function, address order,
;; logical string length, byte conversion, uppercase conversion, and the
;; linked and sconst predicates specialized respectively to t and t_1.

(defstub sc19-memory (address) t)
(defstub sc19-allocation (index) t)
(defstub sc19-region (base) t)
(defstub sc19-addr-le-op (left right) t)
(defstub sc19-length (address) t)
(defstub sc19-to-uint8 (value) t)
(defstub sc19-toupper (value) t)
(defstub sc19-linked-op () t)
(defstub sc19-sconst-op () t)

(defun-sk sc19-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (sc19-address-p address)
      (and
       (integerp (sc19-memory address))
       (integerp (sc19-length address))))
     (implies
      (integerp index)
      (integerp (sc19-allocation index)))
     (implies
      (integerp base)
      (integerp (sc19-region base)))
     (implies
      (integerp value)
      (and
       (integerp (sc19-to-uint8 value))
       (integerp (sc19-toupper value)))))))

(defun sc19-addr-le-p (left right)
  (if (sc19-addr-le-op left right) t nil))

;; This is the exact source law for address order: for addresses with the same
;; base, addr_le is precisely integer order on offsets.

(defun-sk sc19-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (sc19-address-p left)
      (sc19-address-p right)
      (equal
       (sc19-address-base left)
       (sc19-address-base right)))
     (equal
      (sc19-addr-le-p left right)
      (<=
       (sc19-address-offset left)
       (sc19-address-offset right))))))

(defun sc19-linked-p ()
  (if (sc19-linked-op) t nil))

(defun sc19-sconst-p ()
  (if (sc19-sconst-op) t nil))

(defun sc19-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun sc19-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun sc19-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun sc19-is-lower-p (value)
  (and
   (integerp value)
   (<= 97 value)
   (<= value 122)))

(defun sc19-is-upper-p (value)
  (and
   (integerp value)
   (<= 65 value)
   (<= value 90)))

;; These are the imported Cint laws used by the source byte conversion:
;; to_uint8 always returns an unsigned byte and fixes every unsigned byte.

(defun-sk sc19-to-uint8-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sc19-is-uint8-p (sc19-to-uint8 value))
      (implies
       (sc19-is-uint8-p value)
       (equal (sc19-to-uint8 value) value))))))

;; This is the universal closure of A_ToUpper.Q_TL_ToUpper and
;; A_ToUpper.Q_to_upper_char. It preserves the source's nested universal
;; scopes for uppercase and non-alphabetic unsigned bytes.

(defun-sk sc19-toupper-laws-p ()
  (forall (c upper neutral)
    (and
     (implies
      (sc19-is-uint8-p c)
      (sc19-is-sint8-p (sc19-toupper c)))
     (implies
      (and
       (sc19-is-uint8-p c)
       (sc19-is-lower-p c))
      (and
       (equal (+ 32 (sc19-toupper c)) c)
       (implies
        (and
         (sc19-is-uint8-p upper)
         (sc19-is-upper-p upper))
        (and
         (equal (sc19-toupper upper) upper)
         (implies
          (and
           (sc19-is-uint8-p neutral)
           (not (sc19-is-lower-p neutral))
           (not (sc19-is-upper-p neutral)))
          (equal (sc19-toupper neutral) neutral)))))))))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun sc19-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (sc19-address-base address))
    (<= 0 (sc19-address-offset address))
    (<=
     (+ (sc19-address-offset address) length)
     (sc19-allocation (sc19-address-base address))))))

(defun sc19-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (sc19-address-base left)
     (sc19-address-base right)))
   (<=
    (+ (sc19-address-offset right) right-length)
    (sc19-address-offset left))
   (<=
    (+ (sc19-address-offset left) left-length)
    (sc19-address-offset right))))

;; Exact unfolding of Axiomatic.p_length_of_str_is. Its internal index remains
;; universally quantified over every mathematical integer.

(defun-sk sc19-length-of-string-is-p (address length)
  (forall (index)
    (and
     (equal
      (sc19-memory (sc19-shift address length))
      0)
     (<= 0 length)
     (sc19-valid-rw-p
      (sc19-shift address 0)
      (+ 1 length))
     (implies
      (integerp index)
      (implies
       (and
        (<= 0 index)
        (< index length))
       (not
        (equal
         (sc19-memory (sc19-shift address index))
         0)))))))

;; This is A_Length.Q_string_length specialized to the arbitrary memory and
;; allocation functions represented above.

(defun-sk sc19-length-law-p ()
  (forall (address length)
    (implies
     (and
      (sc19-address-p address)
      (integerp length)
      (sc19-length-of-string-is-p address length))
     (equal (sc19-length address) length))))

;; The source conclusion is the negation of this universal equality. The
;; quantified index remains internal rather than becoming a statement
;; parameter.

(defun-sk sc19-prefix-all-equal-p (a a2 x1 x2)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< (+ index x2) x1)
       (equal
        (sc19-toupper
         (sc19-to-uint8
          (sc19-memory (sc19-shift a2 index))))
        (sc19-toupper
         (sc19-to-uint8
          (sc19-memory (sc19-shift a index))))))))))

(defun-sk ntp4vc-strcasecmp-not-eq-post-part2-goal19-statement ()
  (forall
   (a a1 a2 i5 i6 i i1 i4 i2 i3)
   (implies
    (and
     (sc19-address-p a)
     (sc19-address-p a1)
     (sc19-address-p a2)
     (integerp i5)
     (integerp i6)
     (integerp i)
     (integerp i1)
     (integerp i4)
     (integerp i2)
     (integerp i3)
     (sc19-function-types-p)
     (sc19-address-order-law-p)
     (sc19-to-uint8-laws-p)
     (sc19-toupper-laws-p)
     (sc19-length-law-p))
    (let*
        ((x (sc19-address-base a))
         (x1 (sc19-address-offset a1))
         (x2 (sc19-address-offset a))
         (a3 (sc19-shift a2 (- x1 x2)))
         (x3 (sc19-memory a1))
         (x4 (sc19-length a))
         (x5 (sc19-length a2))
         (x6 (sc19-to-uint8 x3)))
      (implies
       (and
        (equal (sc19-address-base a1) x)
        (not
         (equal
          (sc19-toupper
           (sc19-to-uint8
            (sc19-memory (sc19-shift a2 i5))))
          (sc19-toupper
           (sc19-to-uint8
            (sc19-memory (sc19-shift a i5))))))
        (equal (sc19-memory a3) 0)
        (<= 0 i5)
        (<= i5 i6)
        (<= 0 x3)
        (<= (sc19-region x) 0)
        (<= (sc19-region (sc19-address-base a2)) 0)
        (<= x3 255)
        (sc19-linked-p)
        (sc19-sconst-p)
        (sc19-is-sint32-p i)
        (sc19-addr-le-p a a1)
        (sc19-is-sint8-p x3)
        (sc19-length-of-string-is-p a i1)
        (sc19-length-of-string-is-p a i4)
        (sc19-length-of-string-is-p a i6)
        (sc19-length-of-string-is-p a2 i2)
        (sc19-length-of-string-is-p a2 i3)
        (sc19-length-of-string-is-p a2 i6)
        (sc19-addr-le-p a1 (sc19-shift a x4))
        (sc19-separated-p
         (sc19-shift a2 0)
         (+ 1 x5)
         (sc19-shift a 0)
         (+ 1 x4))
        (sc19-addr-le-p a2 a3)
        (sc19-addr-le-p a3 (sc19-shift a2 x5))
        (implies
         (sc19-is-lower-p 0)
         (equal i -32))
        (implies
         (sc19-is-upper-p 0)
         (equal i 0))
        (implies
         (not (sc19-is-lower-p 0))
         (implies
          (not (sc19-is-upper-p 0))
          (equal i 0)))
        (implies
         (sc19-is-upper-p x6)
         (equal x3 i))
        (implies
         (sc19-is-lower-p x6)
         (equal x3 (+ 32 i)))
        (implies
         (not (sc19-is-lower-p x6))
         (implies
          (not (sc19-is-upper-p x6))
          (equal x3 i))))
       (not (sc19-prefix-all-equal-p a a2 x1 x2)))))))

(value-triple :itpeval-statement-checked)

:q
