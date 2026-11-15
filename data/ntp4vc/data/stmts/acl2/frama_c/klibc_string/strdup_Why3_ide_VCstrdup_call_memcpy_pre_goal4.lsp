;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/klibc_string/strdup_Why3_ide_VCstrdup_call_memcpy_pre_goal4:
;; separation of the source string and writable destination regions required
;; before the memcpy call, under the stated string-length, memory-validity,
;; linkedness, constancy, integer-range, and non-null hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sd4-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sd4-address-base (address)
  (car address))

(defun sd4-address-offset (address)
  (cdr address))

(defun sd4-shift (address amount)
  (cons
   (sd4-address-base address)
   (+ (sd4-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; character memory t_1, allocation map t, string-length function, uint32
;; conversion, region function, and the linked and sconst predicates
;; specialized respectively to t and t_1.

(defstub sd4-character-memory (address) t)
(defstub sd4-allocation (index) t)
(defstub sd4-string-length (address) t)
(defstub sd4-to-uint32 (value) t)
(defstub sd4-region (base) t)
(defstub sd4-linked-op () t)
(defstub sd4-sconst-op () t)

(defun-sk sd4-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (sd4-address-p address)
      (and
       (integerp (sd4-character-memory address))
       (integerp (sd4-string-length address))))
     (implies
      (integerp index)
      (integerp (sd4-allocation index)))
     (implies
      (integerp base)
      (integerp (sd4-region base)))
     (implies
      (integerp value)
      (integerp (sd4-to-uint32 value))))))

(defun sd4-linked-p ()
  (if (sd4-linked-op) t nil))

(defun sd4-sconst-p ()
  (if (sd4-sconst-op) t nil))

(defun sd4-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun sd4-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; These are exactly the imported Cint laws is_to_uint32, id_uint32, and
;; proj_uint32 for the arbitrary conversion function.

(defun-sk sd4-to-uint32-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (sd4-is-uint32-p (sd4-to-uint32 value))
      (implies
       (sd4-is-uint32-p value)
       (equal (sd4-to-uint32 value) value))
      (equal
       (sd4-to-uint32 (sd4-to-uint32 value))
       (sd4-to-uint32 value))))))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun sd4-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (sd4-address-base address))
    (<= 0 (sd4-address-offset address))
    (<=
     (+ (sd4-address-offset address) length)
     (sd4-allocation (sd4-address-base address))))))

(defun sd4-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (sd4-address-base left)
     (sd4-address-base right)))
   (<=
    (+ (sd4-address-offset right) right-length)
    (sd4-address-offset left))
   (<=
    (+ (sd4-address-offset left) left-length)
    (sd4-address-offset right))))

;; The source's universal assertion that no null character occurs at any
;; mathematical-integer offset in [0, length).

(defun-sk sd4-no-null-before-p (string length)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position length)
       (not
        (equal
         (sd4-character-memory
          (sd4-shift string position))
         0)))))))

;; Exact unfolding of Axiomatic.p_length_of_str_is.

(defun sd4-p-length-of-str-is-p (string length)
  (and
   (equal
    (sd4-character-memory (sd4-shift string length))
    0)
   (<= 0 length)
   (sd4-valid-rw-p
    (sd4-shift string 0)
    (+ 1 length))
   (sd4-no-null-before-p string length)))

;; This is the imported A_Length.Q_string_length law specialized to the
;; arbitrary source allocation and character-memory functions.

(defun-sk sd4-string-length-law-p ()
  (forall (string length)
    (implies
     (and
      (sd4-address-p string)
      (integerp length)
      (sd4-p-length-of-str-is-p string length))
     (equal
      (sd4-string-length string)
      length))))

(defun-sk
    ntp4vc-strdup-call-memcpy-pre-goal4-statement ()
  (forall
   (a a1 i i1 i2)
   (implies
    (and
     (sd4-address-p a)
     (sd4-address-p a1)
     (integerp i)
     (integerp i1)
     (integerp i2)
     (sd4-function-types-p)
     (sd4-to-uint32-laws-p)
     (sd4-string-length-law-p))
    (let*
        ((x (sd4-string-length a))
         (x1 (+ 1 x))
         (x2 (sd4-to-uint32 x1))
         (a2 (sd4-shift a1 0)))
      (implies
       (and
        (not (equal (cons 0 0) a1))
        (not (equal x2 0))
        (<= (sd4-region (sd4-address-base a)) 0)
        (sd4-linked-p)
        (sd4-sconst-p)
        (sd4-is-sint32-p x)
        (sd4-p-length-of-str-is-p a i)
        (sd4-p-length-of-str-is-p a i1)
        (sd4-p-length-of-str-is-p a i2)
        (sd4-is-sint32-p x1)
        (implies
         (< 0 x2)
         (sd4-valid-rw-p a2 x2)))
       (sd4-separated-p
        (sd4-shift a 0)
        x2
        a2
        x2))))))

(value-triple :itpeval-statement-checked)

:q
