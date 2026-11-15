;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/sysfs_streq_Why3_ide_VCsysfs_streq_assert_13_goal19:
;; the sysfs string-equality verification condition concluding that the
;; newline-terminated second string has logical sysfs length equal to the
;; shared prefix index, under the stated memory, string-validity, comparison,
;; region, linkedness, constancy, and quantified prefix hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun ss13g19-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun ss13g19-address-base (address)
  (car address))

(defun ss13g19-address-offset (address)
  (cdr address))

(defun ss13g19-shift (address amount)
  (cons
   (ss13g19-address-base address)
   (+ (ss13g19-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region, logical
;; strlen, logical sysfs strlen, logical strncmp, C integer conversions,
;; linkedness, and constancy symbols.

(defstub ss13g19-character-memory (address) t)
(defstub ss13g19-allocation (index) t)
(defstub ss13g19-region (base) t)
(defstub ss13g19-l-strlen (address) t)
(defstub ss13g19-l-sysfs-strlen (address) t)
(defstub ss13g19-l-strncmp (left right count) t)
(defstub ss13g19-to-uint64 (value) t)
(defstub ss13g19-to-sint32 (value) t)
(defstub ss13g19-linked-op () t)
(defstub ss13g19-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk ss13g19-function-types-p ()
  (forall (address index base value left right count)
    (and
     (implies
      (ss13g19-address-p address)
      (and
       (integerp
        (ss13g19-character-memory address))
       (integerp
        (ss13g19-l-strlen address))
       (integerp
        (ss13g19-l-sysfs-strlen address))))
     (implies
      (integerp index)
      (integerp
       (ss13g19-allocation index)))
     (implies
      (integerp base)
      (integerp
       (ss13g19-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (ss13g19-to-uint64 value))
       (integerp
        (ss13g19-to-sint32 value))))
     (implies
      (and
       (ss13g19-address-p left)
       (ss13g19-address-p right)
       (integerp count))
      (integerp
       (ss13g19-l-strncmp left right count))))))

(defun ss13g19-linked-p ()
  (if (ss13g19-linked-op) t nil))

(defun ss13g19-sconst-p ()
  (if (ss13g19-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun ss13g19-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun ss13g19-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun ss13g19-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by the three logical string recurrences.

(defun-sk ss13g19-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (ss13g19-is-uint64-p
       (ss13g19-to-uint64 value))
      (implies
       (ss13g19-is-uint64-p value)
       (equal
        (ss13g19-to-uint64 value)
        value))
      (equal
       (ss13g19-to-uint64
        (ss13g19-to-uint64 value))
       (ss13g19-to-uint64 value))))))

(defun-sk ss13g19-to-sint32-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (ss13g19-is-sint32-p
       (ss13g19-to-sint32 value))
      (implies
       (ss13g19-is-sint32-p value)
       (equal
        (ss13g19-to-sint32 value)
        value))
      (equal
       (ss13g19-to-sint32
        (ss13g19-to-sint32 value))
       (ss13g19-to-sint32 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun ss13g19-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (ss13g19-address-base address))
    (<= 0
        (ss13g19-address-offset address))
    (<=
     (+ (ss13g19-address-offset address)
        length)
     (ss13g19-allocation
      (ss13g19-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. Its null terminator remains an
;; internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk ss13g19-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (ss13g19-is-sint8-p
       (ss13g19-character-memory
        (ss13g19-shift address position)))))))

(defun-sk ss13g19-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (ss13g19-character-memory
       (ss13g19-shift address index))
      0)
     (ss13g19-is-uint64-p index)
     (ss13g19-valid-rw-p
      (ss13g19-shift address 0)
      (+ 1 index))
     (ss13g19-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk ss13g19-strlen-laws-p ()
  (forall (address)
    (implies
     (ss13g19-address-p address)
     (and
      (if
          (equal
           (ss13g19-character-memory
            (ss13g19-shift address 0))
           0)
          (equal
           (ss13g19-l-strlen address)
           0)
        (equal
         (ss13g19-to-uint64
          (+ 1
             (ss13g19-l-strlen
              (ss13g19-shift address 1))))
         (ss13g19-l-strlen address)))
      (ss13g19-is-uint64-p
       (ss13g19-l-strlen address))))))

;; Universal closures of A_SysfsStr.fix_l_sysfs_strlen and
;; Q_TL_sysfs_strlen.

(defun-sk ss13g19-sysfs-strlen-laws-p ()
  (forall (address)
    (implies
     (ss13g19-address-p address)
     (and
      (if
          (or
           (equal
            (ss13g19-character-memory
             (ss13g19-shift address 0))
            0)
           (and
            (equal
             (ss13g19-character-memory
              (ss13g19-shift address 0))
             10)
            (equal
             (ss13g19-character-memory
              (ss13g19-shift address 1))
             0)))
          (equal
           (ss13g19-l-sysfs-strlen address)
           0)
        (equal
         (ss13g19-to-uint64
          (+ 1
             (ss13g19-l-sysfs-strlen
              (ss13g19-shift address 1))))
         (ss13g19-l-sysfs-strlen address)))
      (ss13g19-is-uint64-p
       (ss13g19-l-sysfs-strlen address))))))

;; Universal closures of A_StrnCmp.fix_l_strncmp_2' and Q_TL_strncmp_2'.

(defun-sk ss13g19-strncmp-laws-p ()
  (forall (left right count)
    (implies
     (and
      (ss13g19-address-p left)
      (ss13g19-address-p right)
      (integerp count))
     (and
      (if
          (equal count 0)
          (equal
           (ss13g19-l-strncmp left right count)
           0)
        (if
            (equal
             (ss13g19-character-memory
              (ss13g19-shift right 0))
             (ss13g19-character-memory
              (ss13g19-shift left 0)))
            (if
                (equal
                 (ss13g19-character-memory
                  (ss13g19-shift left 0))
                 0)
                (equal
                 (ss13g19-l-strncmp left right count)
                 0)
              (equal
               (ss13g19-l-strncmp
                (ss13g19-shift left 1)
                (ss13g19-shift right 1)
                (ss13g19-to-uint64 (- count 1)))
               (ss13g19-l-strncmp left right count)))
          (equal
           (ss13g19-to-sint32
            (-
             (ss13g19-character-memory
              (ss13g19-shift left 0))
             (ss13g19-character-memory
              (ss13g19-shift right 0))))
           (ss13g19-l-strncmp left right count))))
      (ss13g19-is-sint32-p
       (ss13g19-l-strncmp left right count))))))

(defun ss13g19-strnequal-p (left right count)
  (equal
   (ss13g19-l-strncmp left right count)
   0))

;; The two source prefix hypotheses retain their universal quantifiers over
;; every mathematical integer and their original strict upper bound.

(defun-sk ss13g19-prefix-equal-before-p
    (left right bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position bound)
       (equal
        (ss13g19-character-memory
         (ss13g19-shift left position))
        (ss13g19-character-memory
         (ss13g19-shift right position))))))))

(defun-sk ss13g19-prefix-nonzero-and-equal-before-p
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
          (ss13g19-character-memory
           (ss13g19-shift right position))
          0))
        (not
         (equal
          (ss13g19-character-memory
           (ss13g19-shift left position))
          0))
        (equal
         (ss13g19-character-memory
          (ss13g19-shift left position))
         (ss13g19-character-memory
          (ss13g19-shift right position)))))))))

(defun-sk
    ntp4vc-sysfs-streq-assert-13-goal19-statement ()
  (forall
   (a i a1)
   (implies
    (and
     (ss13g19-address-p a)
     (integerp i)
     (ss13g19-address-p a1)
     (ss13g19-function-types-p)
     (ss13g19-to-uint64-laws-p)
     (ss13g19-to-sint32-laws-p)
     (ss13g19-strlen-laws-p)
     (ss13g19-sysfs-strlen-laws-p)
     (ss13g19-strncmp-laws-p))
    (let*
        ((a2
          (ss13g19-shift a i))
         (a3
          (ss13g19-shift a1 i))
         (x
          (ss13g19-l-sysfs-strlen a3)))
      (implies
       (and
        (equal
         (ss13g19-character-memory a2)
         0)
        (equal
         (ss13g19-character-memory a3)
         10)
        (equal
         x
         (ss13g19-l-sysfs-strlen a2))
        (equal
         (ss13g19-character-memory
          (ss13g19-shift a1 (+ 1 i)))
         0)
        (<= i
            (ss13g19-l-strlen a))
        (<= i
            (ss13g19-l-strlen a1))
        (<=
         (ss13g19-region
          (ss13g19-address-base a))
         0)
        (<=
         (ss13g19-region
          (ss13g19-address-base a1))
         0)
        (ss13g19-linked-p)
        (ss13g19-sconst-p)
        (ss13g19-is-uint64-p i)
        (ss13g19-valid-string-p a)
        (ss13g19-valid-string-p a1)
        (ss13g19-strnequal-p a1 a i)
        (ss13g19-valid-string-p a2)
        (ss13g19-valid-string-p a3)
        (ss13g19-strnequal-p a3 a2 x)
        (ss13g19-prefix-equal-before-p
         a1 a i)
        (ss13g19-prefix-nonzero-and-equal-before-p
         a1 a i))
       (equal
        (ss13g19-l-sysfs-strlen a1)
        i))))))

(value-triple :itpeval-statement-checked)

:q
