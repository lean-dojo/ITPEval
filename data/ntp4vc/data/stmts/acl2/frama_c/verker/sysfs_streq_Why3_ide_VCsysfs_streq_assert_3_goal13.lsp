;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/sysfs_streq_Why3_ide_VCsysfs_streq_assert_3_goal13:
;; null bytes at the two shifted string positions, together with the stated
;; memory, string-validity, comparison, region, linkedness, constancy, and
;; quantified prefix hypotheses, imply equal logical sysfs string lengths.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun ss3g13-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun ss3g13-address-base (address)
  (car address))

(defun ss3g13-address-offset (address)
  (cdr address))

(defun ss3g13-shift (address amount)
  (cons
   (ss3g13-address-base address)
   (+ (ss3g13-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region, logical
;; strlen, logical sysfs strlen, logical strncmp, C integer conversions,
;; linkedness, and constancy symbols.

(defstub ss3g13-character-memory (address) t)
(defstub ss3g13-allocation (index) t)
(defstub ss3g13-region (base) t)
(defstub ss3g13-l-strlen (address) t)
(defstub ss3g13-l-sysfs-strlen (address) t)
(defstub ss3g13-l-strncmp (left right count) t)
(defstub ss3g13-to-uint32 (value) t)
(defstub ss3g13-to-sint32 (value) t)
(defstub ss3g13-to-uint64 (value) t)
(defstub ss3g13-to-sint64 (value) t)
(defstub ss3g13-linked-op () t)
(defstub ss3g13-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk ss3g13-function-types-p ()
  (forall (address index base value left right count)
    (and
     (implies
      (ss3g13-address-p address)
      (and
       (integerp
        (ss3g13-character-memory address))
       (integerp
        (ss3g13-l-strlen address))
       (integerp
        (ss3g13-l-sysfs-strlen address))))
     (implies
      (integerp index)
      (integerp
       (ss3g13-allocation index)))
     (implies
      (integerp base)
      (integerp
       (ss3g13-region base)))
     (implies
     (integerp value)
      (and
       (integerp
        (ss3g13-to-uint32 value))
       (integerp
        (ss3g13-to-sint32 value))
       (integerp
        (ss3g13-to-uint64 value))
       (integerp
        (ss3g13-to-sint64 value))))
     (implies
      (and
       (ss3g13-address-p left)
       (ss3g13-address-p right)
       (integerp count))
      (integerp
       (ss3g13-l-strncmp left right count))))))

(defun ss3g13-linked-p ()
  (if (ss3g13-linked-op) t nil))

(defun ss3g13-sconst-p ()
  (if (ss3g13-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun ss3g13-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun ss3g13-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun ss3g13-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun ss3g13-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

(defun ss3g13-is-sint64-p (value)
  (and
   (integerp value)
   (<= -9223372036854775808 value)
   (< value 9223372036854775808)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by the logical string recurrences.

(defun-sk ss3g13-to-uint32-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (ss3g13-is-uint32-p
       (ss3g13-to-uint32 value))
      (implies
       (ss3g13-is-uint32-p value)
       (equal
        (ss3g13-to-uint32 value)
        value))
      (equal
       (ss3g13-to-uint32
        (ss3g13-to-uint32 value))
       (ss3g13-to-uint32 value))))))

(defun-sk ss3g13-to-sint32-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (ss3g13-is-sint32-p
       (ss3g13-to-sint32 value))
      (implies
       (ss3g13-is-sint32-p value)
       (equal
        (ss3g13-to-sint32 value)
        value))
      (equal
       (ss3g13-to-sint32
        (ss3g13-to-sint32 value))
       (ss3g13-to-sint32 value))))))

(defun-sk ss3g13-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (ss3g13-is-uint64-p
       (ss3g13-to-uint64 value))
      (implies
       (ss3g13-is-uint64-p value)
       (equal
        (ss3g13-to-uint64 value)
        value))
      (equal
       (ss3g13-to-uint64
       (ss3g13-to-uint64 value))
       (ss3g13-to-uint64 value))))))

(defun-sk ss3g13-to-sint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (ss3g13-is-sint64-p
       (ss3g13-to-sint64 value))
      (implies
       (ss3g13-is-sint64-p value)
       (equal
        (ss3g13-to-sint64 value)
        value))
      (equal
       (ss3g13-to-sint64
        (ss3g13-to-sint64 value))
       (ss3g13-to-sint64 value))))))

;; Exact Cint.proj_int32 and Cint.proj_int64 interaction laws.

(defun-sk ss3g13-signed-unsigned-projection-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (equal
       (ss3g13-to-sint32
        (ss3g13-to-uint32 value))
       (ss3g13-to-sint32 value))
      (equal
       (ss3g13-to-sint64
        (ss3g13-to-uint64 value))
       (ss3g13-to-sint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun ss3g13-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (ss3g13-address-base address))
    (<= 0
        (ss3g13-address-offset address))
    (<=
     (+ (ss3g13-address-offset address)
        length)
     (ss3g13-allocation
      (ss3g13-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. Its null terminator remains an
;; internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk ss3g13-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (ss3g13-is-sint8-p
       (ss3g13-character-memory
        (ss3g13-shift address position)))))))

(defun-sk ss3g13-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (ss3g13-character-memory
       (ss3g13-shift address index))
      0)
     (ss3g13-is-uint64-p index)
     (ss3g13-valid-rw-p
      (ss3g13-shift address 0)
      (+ 1 index))
     (ss3g13-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk ss3g13-strlen-laws-p ()
  (forall (address)
    (implies
     (ss3g13-address-p address)
     (and
      (if
          (equal
           (ss3g13-character-memory
            (ss3g13-shift address 0))
           0)
          (equal
           (ss3g13-l-strlen address)
           0)
        (equal
         (ss3g13-to-uint64
          (+ 1
             (ss3g13-l-strlen
              (ss3g13-shift address 1))))
         (ss3g13-l-strlen address)))
      (ss3g13-is-uint64-p
       (ss3g13-l-strlen address))))))

;; Universal closures of A_SysfsStr.fix_l_sysfs_strlen and
;; Q_TL_sysfs_strlen.

(defun-sk ss3g13-sysfs-strlen-laws-p ()
  (forall (address)
    (implies
     (ss3g13-address-p address)
     (and
      (if
          (or
           (equal
            (ss3g13-character-memory
             (ss3g13-shift address 0))
            0)
           (and
            (equal
             (ss3g13-character-memory
              (ss3g13-shift address 0))
             10)
            (equal
             (ss3g13-character-memory
              (ss3g13-shift address 1))
             0)))
          (equal
           (ss3g13-l-sysfs-strlen address)
           0)
        (equal
         (ss3g13-to-uint64
          (+ 1
             (ss3g13-l-sysfs-strlen
              (ss3g13-shift address 1))))
         (ss3g13-l-sysfs-strlen address)))
      (ss3g13-is-uint64-p
       (ss3g13-l-sysfs-strlen address))))))

;; Universal closures of A_StrnCmp.fix_l_strncmp_2' and Q_TL_strncmp_2'.

(defun-sk ss3g13-strncmp-laws-p ()
  (forall (left right count)
    (implies
     (and
      (ss3g13-address-p left)
      (ss3g13-address-p right)
      (integerp count))
     (and
      (if
          (equal count 0)
          (equal
           (ss3g13-l-strncmp left right count)
           0)
        (if
            (equal
             (ss3g13-character-memory
              (ss3g13-shift right 0))
             (ss3g13-character-memory
              (ss3g13-shift left 0)))
            (if
                (equal
                 (ss3g13-character-memory
                  (ss3g13-shift left 0))
                 0)
                (equal
                 (ss3g13-l-strncmp left right count)
                 0)
              (equal
               (ss3g13-l-strncmp
                (ss3g13-shift left 1)
                (ss3g13-shift right 1)
                (ss3g13-to-uint64 (- count 1)))
               (ss3g13-l-strncmp left right count)))
          (equal
           (ss3g13-to-sint32
            (-
             (ss3g13-character-memory
              (ss3g13-shift left 0))
             (ss3g13-character-memory
              (ss3g13-shift right 0))))
           (ss3g13-l-strncmp left right count))))
      (ss3g13-is-sint32-p
       (ss3g13-l-strncmp left right count))))))

(defun ss3g13-strnequal-p (left right count)
  (equal
   (ss3g13-l-strncmp left right count)
   0))

;; The two source prefix hypotheses retain their universal quantifiers over
;; every mathematical integer and their original strict upper bound.

(defun-sk ss3g13-prefix-equal-before-p
    (left right bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position bound)
       (equal
        (ss3g13-character-memory
         (ss3g13-shift left position))
        (ss3g13-character-memory
         (ss3g13-shift right position))))))))

(defun-sk ss3g13-prefix-nonzero-and-equal-before-p
    (left right bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position bound)
       (and
        (not
         (equal
          (ss3g13-character-memory
           (ss3g13-shift right position))
          0))
        (not
         (equal
          (ss3g13-character-memory
           (ss3g13-shift left position))
          0))
        (equal
         (ss3g13-character-memory
          (ss3g13-shift left position))
         (ss3g13-character-memory
          (ss3g13-shift right position)))))))))

(defun-sk
    ntp4vc-sysfs-streq-assert-3-goal13-statement ()
  (forall
   (a i a1)
   (implies
    (and
     (ss3g13-address-p a)
     (integerp i)
     (ss3g13-address-p a1)
     (ss3g13-function-types-p)
     (ss3g13-to-uint32-laws-p)
     (ss3g13-to-sint32-laws-p)
     (ss3g13-to-uint64-laws-p)
     (ss3g13-to-sint64-laws-p)
     (ss3g13-signed-unsigned-projection-laws-p)
     (ss3g13-strlen-laws-p)
     (ss3g13-sysfs-strlen-laws-p)
     (ss3g13-strncmp-laws-p))
    (let*
        ((a2
          (ss3g13-shift a i))
         (a3
          (ss3g13-shift a1 i)))
      (implies
       (and
        (equal
         (ss3g13-character-memory a2)
         0)
        (equal
         (ss3g13-character-memory a3)
         0)
        (<= i
            (ss3g13-l-strlen a))
        (<= i
            (ss3g13-l-strlen a1))
        (<=
         (ss3g13-region
          (ss3g13-address-base a))
         0)
        (<=
         (ss3g13-region
          (ss3g13-address-base a1))
         0)
        (ss3g13-linked-p)
        (ss3g13-sconst-p)
        (ss3g13-is-uint64-p i)
        (ss3g13-valid-string-p a)
        (ss3g13-valid-string-p a1)
        (ss3g13-strnequal-p a1 a i)
        (ss3g13-valid-string-p a2)
        (ss3g13-valid-string-p a3)
        (ss3g13-prefix-equal-before-p
         a1 a i)
        (ss3g13-prefix-nonzero-and-equal-before-p
         a1 a i))
       (equal
        (ss3g13-l-sysfs-strlen a1)
        (ss3g13-l-sysfs-strlen a)))))))

(value-triple :itpeval-statement-checked)

:q
