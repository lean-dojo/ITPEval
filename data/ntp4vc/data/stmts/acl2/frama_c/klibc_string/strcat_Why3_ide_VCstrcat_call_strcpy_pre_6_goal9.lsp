;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/klibc_string/strcat_Why3_ide_VCstrcat_call_strcpy_pre_6_goal9:
;; separation of the source and destination string regions required before
;; the strcpy call, under the stated memory-validity, string-length,
;; address-order, linkedness, constancy, and null-character hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sc9-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sc9-address-base (address)
  (car address))

(defun sc9-address-offset (address)
  (cdr address))

(defun sc9-shift (address amount)
  (cons
   (sc9-address-base address)
   (+ (sc9-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; character memory t_1, allocation map t, string-length function, region
;; function, address-order relation, signed-byte conversion, and the linked
;; and sconst predicates specialized respectively to t and t_1.

(defstub sc9-character-memory (address) t)
(defstub sc9-allocation (index) t)
(defstub sc9-string-length (address) t)
(defstub sc9-region (base) t)
(defstub sc9-addr-le-op (left right) t)
(defstub sc9-to-sint8 (value) t)
(defstub sc9-linked-op () t)
(defstub sc9-sconst-op () t)

(defun-sk sc9-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (sc9-address-p address)
      (and
       (integerp (sc9-character-memory address))
       (integerp (sc9-string-length address))))
     (implies
      (integerp index)
      (integerp (sc9-allocation index)))
     (implies
      (integerp base)
      (integerp (sc9-region base)))
     (implies
      (integerp value)
      (integerp (sc9-to-sint8 value))))))

(defun sc9-addr-le-p (left right)
  (if (sc9-addr-le-op left right) t nil))

;; This is the exact source law for address order: when two addresses have the
;; same base, addr_le is precisely integer order on their offsets.

(defun-sk sc9-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (sc9-address-p left)
      (sc9-address-p right)
      (equal
       (sc9-address-base left)
       (sc9-address-base right)))
     (equal
      (sc9-addr-le-p left right)
      (<=
       (sc9-address-offset left)
       (sc9-address-offset right))))))

(defun sc9-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

;; This is the imported Cint.id_sint8 law.

(defun-sk sc9-cint-law-p ()
  (forall (value)
    (implies
     (sc9-is-sint8-p value)
     (equal (sc9-to-sint8 value) value))))

(defun sc9-linked-p ()
  (if (sc9-linked-op) t nil))

(defun sc9-sconst-p ()
  (if (sc9-sconst-op) t nil))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun sc9-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (sc9-address-base address))
    (<= 0 (sc9-address-offset address))
    (<=
     (+ (sc9-address-offset address) length)
     (sc9-allocation (sc9-address-base address))))))

(defun sc9-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (sc9-address-base left)
     (sc9-address-base right)))
   (<=
    (+ (sc9-address-offset right) right-length)
    (sc9-address-offset left))
   (<=
    (+ (sc9-address-offset left) left-length)
    (sc9-address-offset right))))

;; The source's universally quantified assertion that a character value is
;; absent at every mathematical-integer offset in [0, limit).

(defun-sk sc9-no-value-before-p (string value limit)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position limit)
       (not
        (equal
         (sc9-character-memory
          (sc9-shift string position))
         value)))))))

;; Exact unfolding of Axiomatic.p_length_of_str_is.

(defun sc9-p-length-of-str-is-p (string length)
  (and
   (equal
    (sc9-character-memory (sc9-shift string length))
    0)
   (<= 0 length)
   (sc9-valid-rw-p
    (sc9-shift string 0)
    (+ 1 length))
   (sc9-no-value-before-p string 0 length)))

;; This is the imported A_Length.Q_string_length law specialized to the
;; arbitrary source allocation and character-memory functions.

(defun-sk sc9-string-length-law-p ()
  (forall (string length)
    (implies
     (and
      (sc9-address-p string)
      (integerp length)
      (sc9-p-length-of-str-is-p string length))
     (equal
      (sc9-string-length string)
      length))))

;; Exact existence of a null character at a mathematical-integer offset in
;; [0, limit).

(defun-sk sc9-zero-in-prefix-p (string limit)
  (exists (position)
    (and
     (integerp position)
     (equal
      (sc9-character-memory
       (sc9-shift string position))
      0)
     (<= 0 position)
     (< position limit))))

;; Exact unfolding of Axiomatic1.p_exists_first_occurence_of_char.

(defun sc9-p-exists-first-occurrence-of-char-p
    (string char-value position)
  (let*
      ((converted-character (sc9-to-sint8 char-value))
       (length (sc9-string-length string)))
    (and
     (equal
      (sc9-character-memory
       (sc9-shift string position))
      converted-character)
     (<= 0 position)
     (<= position length)
     (<= -128 char-value)
     (<= char-value 127)
     (sc9-valid-rw-p
      (sc9-shift string 0)
      (+ 1 length))
     (sc9-no-value-before-p
      string
      converted-character
      position))))

(defun-sk
    ntp4vc-strcat-call-strcpy-pre-6-goal9-statement ()
  (forall
   (a2 a a1 i i3 i1 i2 i4)
   (implies
    (and
     (sc9-address-p a2)
     (sc9-address-p a)
     (sc9-address-p a1)
     (integerp i)
     (integerp i3)
     (integerp i1)
     (integerp i2)
     (integerp i4)
     (sc9-function-types-p)
     (sc9-address-order-law-p)
     (sc9-cint-law-p)
     (sc9-string-length-law-p))
    (let*
        ((x (sc9-address-base a2))
         (x1 (sc9-character-memory a))
         (a3 (sc9-shift a2 0))
         (x2 (sc9-string-length a1))
         (x3 (sc9-string-length a2))
         (a4 (sc9-shift a1 0))
         (x4 (+ 1 x2))
         (zero-in-source
          (sc9-zero-in-prefix-p a2 x3)))
      (implies
       (and
        (<= (sc9-region (sc9-address-base a1)) 0)
        (<= (sc9-region x) 0)
        (sc9-linked-p)
        (sc9-sconst-p)
        (sc9-is-sint8-p x1)
        (sc9-p-length-of-str-is-p a1 i)
        (sc9-p-length-of-str-is-p a1 i3)
        (sc9-p-length-of-str-is-p a2 i1)
        (sc9-p-length-of-str-is-p a2 i2)
        (sc9-p-length-of-str-is-p a2 i4)
        (sc9-valid-rw-p a3 (+ x2 x3))
        (sc9-separated-p a3 (+ 1 x3) a4 x4)
        (implies
         (sc9-no-value-before-p a2 0 x3)
         (equal (cons 0 0) a))
        (implies
         zero-in-source
         (equal x1 0))
        (implies
         zero-in-source
         (equal x (sc9-address-base a)))
        (implies
         zero-in-source
         (sc9-p-exists-first-occurrence-of-char-p
          a2
          0
          (- (sc9-address-offset a)
             (sc9-address-offset a2))))
        (implies
         zero-in-source
         (and
          (sc9-addr-le-p a2 a)
          (sc9-addr-le-p a (sc9-shift a2 x3)))))
       (sc9-separated-p
        a4
        x4
        (sc9-shift a 0)
        x4))))))

(value-triple :itpeval-statement-checked)

:q
