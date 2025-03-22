IN: nrbf;

USING: accessors alien.c-types alien.enums alien.syntax arrays assocs calendar
combinators endian io io.encodings io.encodings.binary io.encodings.utf8
io.files kernel make math math.bitwise pack sequences ;

! MS-NRBF Reader
DEFER: read-record

! Lower level readers
: read-int32 ( -- n )
    "i" read-packed-le first ;

! read a ULEB128 encoded number
: read-uleb128 ( -- n )
    0 [ read1 [ 6 0 bit-range + ] [ 7 bit? ] bi ] [ 7 shift ] do while ; 

! read length-prefixed-string
: read-lpstring ( -- str )
    read-uleb128 utf8 [ read ] with-decoded-input ;

ENUM: binary-type < uchar
    { Primitive 0 }
    { String 1 }
    { Object 2 }
    { SystemClass 3 }
    { Class 4 }
    { ObjectArray 5 }
    { StringArray 6 }
    { PrimitiveArray 7 } ;

ENUM: primitive-type < uchar
    { Boolean 1 }
    { Byte 2 }
    { Char 3 }
    { Decimal 5 }
    { Double 6 }
    { Int16 7 }
    { Int32 8 }
    { Int64 9 }
    { SByte 10 }
    { Single 11 }
    { TimeSpan 12 }
    { DateTime 13 }
    { UInt16 14 }
    { UInt32 15 }
    { UInt64 16 }
    { Null 17 }
    { PrimitiveString 18 }               ! Not allowed in MS-NRBF
    ;

ENUM: record-type < uchar
    { SerializedStreamHeader 0 }
    { ClassWithId 1 }
    { SystemClassWithMembers 2 }
    { ClassWithMembers 3 }
    { SystemClassWithMembersAndTypes 4 }
    { ClassWithMembersAndTypes 5 }
    { BinaryObjectString 6 }
    { BinaryArray 7 }
    { MemberPrimitiveTyped 8 }
    { MemberReference 9 }
    { ObjectNull 10 }
    { MessageEnd 11 }
    { BinaryLibrary 12 }
    { ObjectMultiple256 13 }
    { ObjectNullMultiple 14 }
    { ArraySinglePrimitive 15 }
    { ArraySingleObject 16 }
    { ArraySingleString 17 }
    { MethodCall 21 }
    { MethodReturn 22 }
    ;

: read-enum ( enum-class -- value )
    read1 swap number>enum ; inline

! Reading Encoded Values
ERROR: unsupported-primitive-member enum ;

: DateTime>timestamp ( int64 -- timestamp )
    ! FIXME: negative tick counts!
    [ 63 62 bit-range ] [ 61 0 bit-range ] bi 100 * nanoseconds 0001 <year-gmt> time+ swap
    { { 0 [ ] }
      { 1 [ utc ] }
      { 2 [ local-time ] }
    } case ;

GENERIC: read-primitive-member ( enum -- value )
M: object read-primitive-member unsupported-primitive-member ;
M: Int32 read-primitive-member drop 4 read signed-le> ;
M: Single read-primitive-member drop 4 read le> bits>float ;
M: DateTime read-primitive-member drop 8 read le> DateTime>timestamp ;
M: Byte read-primitive-member drop read1 ;


! Fill a newly created record with data
GENERIC: read-new-record ( record -- record )

! Note: record-type-enums are implied.  If needed for writing: define generic to output them, or reverse-lookup.

TUPLE: serialization-header-record
    root-id
    header-id
    major-version
    minor-version ;

M: serialization-header-record read-new-record
    read-int32 >>root-id
    read-int32 >>header-id
    read-int32 >>major-version
    read-int32 >>minor-version ;

TUPLE: binary-library
    library-id
    library-name ;

M: binary-library read-new-record
    read-int32 >>library-id
    read-lpstring >>library-name ;

TUPLE: class-info
    object-id
    name
    member-count
    member-names
    ;

: read-class-info ( -- class-info )
    class-info new
    read-int32 >>object-id
    read-lpstring >>name
    read-int32 [ >>member-count ] keep
    [ read-lpstring ] replicate >>member-names ;

TUPLE: class-type-info
    type-name
    library-id ;

: read-class-type-info ( -- class-type-info )
    class-type-info new
    read-lpstring >>type-name
    read-int32 >>library-id ;

TUPLE: member-type-info
    binary-type-enums
    additional-infos
    ;

GENERIC: read-additional-info ( enum -- info )
M: object read-additional-info drop f ;

M: Primitive read-additional-info drop primitive-type read-enum ;
M: SystemClass read-additional-info drop read-lpstring ;
M: Class read-additional-info drop read-class-type-info ;
M: PrimitiveArray read-additional-info drop primitive-type read-enum ;

: read-additional-infos ( binary-type-enums -- additional-infos )
    [ read-additional-info ] map ;

: read-member-type-info ( count -- member-type-info )
    member-type-info new swap
    [ binary-type read-enum ] replicate [ >>binary-type-enums ] keep
    read-additional-infos >>additional-infos ;

TUPLE: class-record
    class-info
    member-type-info
    members
    ;

: read-members ( class-record -- members )
    member-type-info>>
    [ additional-infos>> ] [ binary-type-enums>> ] bi
    [ Primitive? [ read-primitive-member ]
      [ drop read-record ] if ]
    collector [ 2each ] dip ;

M: class-record read-new-record
    read-class-info [ >>class-info ] keep
    member-count>> read-member-type-info
    >>member-type-info ;

: read-class-record-members ( class-record -- class-record )
    dup read-members >>members ;

TUPLE: class-with-members-and-types < class-record
   library-id ;

M: class-with-members-and-types read-new-record
    call-next-method
    read-int32 >>library-id
    read-class-record-members ;

TUPLE: array-info
    object-id
    length ;

: read-array-info ( -- array-info )
    array-info new
    read-int32 >>object-id
    read-int32 >>length ;

TUPLE: array-record
    array-info
    members ;

M: array-record read-new-record
    read-array-info >>array-info ;

TUPLE: array-single-primitive < array-record
    primitive-type-enum ;

M: array-single-primitive read-new-record
    call-next-method
    primitive-type read-enum >>primitive-type-enum
    dup [ array-info>> length>> ] [ primitive-type-enum>> ] bi
    '[ _ read-primitive-member ] replicate >>members ;


TUPLE: binary-object-string
    object-id
    value ;

M: binary-object-string read-new-record
    read-int32 >>object-id
    read-lpstring >>value ;

TUPLE: member-reference
    id-ref ;

M: member-reference read-new-record
    read-int32 >>id-ref ;

TUPLE: message-end ;
M: message-end read-new-record ;

! Main record dispatch

ERROR: unsupported-record-type-enum type ;

: record-type>class ( type -- class )
    H{
        { SerializedStreamHeader serialization-header-record }
        { BinaryObjectString binary-object-string }
        { ClassWithMembersAndTypes class-with-members-and-types }
        { MemberReference member-reference }
        { MessageEnd message-end }
        { BinaryLibrary binary-library }
        { ArraySinglePrimitive array-single-primitive }
    } ?at [ unsupported-record-type-enum ] unless ;

: read-record ( -- record/f )
    record-type read-enum [ record-type>class new read-new-record ] [ f ] if* ;

! Unstructured sequence of records
: read-nrbf-records ( path -- records )
    binary [ [ [ read-record dup [ , ] when* ] loop ] V{ } make ] with-file-reader >array ;
