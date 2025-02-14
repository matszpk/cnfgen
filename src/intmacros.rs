// intmacros.rs - integer expression macros

#![cfg_attr(docsrs, feature(doc_cfg))]
//! The module with macro helpers.

#[macro_export]
#[doc(hidden)]
macro_rules! impl_int_ty1_lt_ty2 {
    ($impl_mac:ident) => {
        // 1 < 0b1Y
        $impl_mac!(U1, UInt<UInt<UTerm, B1>, Y0>, Y0);
        // 1 < 0b1YY
        $impl_mac!(U1, UInt<UInt<UInt<UTerm, B1>, Y1>, Y0>, Y0, Y1);
        // 1 < 0b1YYY
        $impl_mac!(
            U1,
            UInt<UInt<UInt<UInt<UTerm, B1>, Y2>, Y1>, Y0>,
            Y0,
            Y1,
            Y2
        );
        // 1 < 0b1YYYY
        $impl_mac!(
            U1,
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y3>, Y2>, Y1>, Y0>,
            Y0,
            Y1,
            Y2,
            Y3
        );
        // 1 < 0b1YYYYY
        $impl_mac!(
            U1,
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y4>, Y3>, Y2>, Y1>, Y0>,
            Y0,
            Y1,
            Y2,
            Y3,
            Y4
        );
        // 1 < 0b1YYYYYY
        $impl_mac!(
            U1,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>,
            Y0,
            Y1,
            Y2,
            Y3,
            Y4,
            Y5
        );
        // 1 < 0b1YYYYYYY
        $impl_mac!(
            U1,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y6>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>,
            Y0,
            Y1,
            Y2,
            Y3,
            Y4,
            Y5,
            Y6
        );

        //---------------------
        // 2 < 3
        $impl_mac!(U2, U3,);
        // 0b1X < 0b1YY
        $impl_mac!(
            UInt<UInt<UTerm, B1>, X0>,
            UInt<UInt<UInt<UTerm, B1>, Y1>, Y0>,
            X0,
            Y0,
            Y1
        );
        // 0b1X < 0b1YYY
        $impl_mac!(
            UInt<UInt<UTerm, B1>, X0>,
            UInt<UInt<UInt<UInt<UTerm, B1>, Y2>, Y1>, Y0>,
            X0,
            Y0,
            Y1,
            Y2
        );
        // 0b1X < 0b1YYYY
        $impl_mac!(
            UInt<UInt<UTerm, B1>, X0>,
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y3>, Y2>, Y1>, Y0>,
            X0,
            Y0,
            Y1,
            Y2,
            Y3
        );
        // 0b1X < 0b1YYYYY
        $impl_mac!(
            UInt<UInt<UTerm, B1>, X0>,
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y4>, Y3>, Y2>, Y1>, Y0>,
            X0,
            Y0,
            Y1,
            Y2,
            Y3,
            Y4
        );
        // 0b1X < 0b1YYYYYY
        $impl_mac!(
            UInt<UInt<UTerm, B1>, X0>,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>,
            X0,
            Y0,
            Y1,
            Y2,
            Y3,
            Y4,
            Y5
        );
        // 0b1X < 0b1YYYYYYY
        $impl_mac!(
            UInt<UInt<UTerm, B1>, X0>,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y6>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>,
            X0,
            Y0,
            Y1,
            Y2,
            Y3,
            Y4,
            Y5,
            Y6
        );

        //---------------------
        // 0b100 < 0b101
        $impl_mac!(U4, U5,);
        // 0b10X < 0b11Y
        $impl_mac!(
            UInt<UInt<UInt<UTerm, B1>, B0>, X0>,
            UInt<UInt<UInt<UTerm, B1>, B1>, Y0>,
            X0,
            Y0
        );
        // 0b110 < 0b111
        $impl_mac!(U6, U7,);
        //---------------------
        // 0b1XX < 0b1YYY
        $impl_mac!(
            UInt<UInt<UInt<UTerm, B1>, X1>, X0>,
            UInt<UInt<UInt<UInt<UTerm, B1>, Y2>, Y1>, Y0>,
            X0,
            X1,
            Y0,
            Y1,
            Y2
        );
        // 0b1XX < 0b1YYYY
        $impl_mac!(
            UInt<UInt<UInt<UTerm, B1>, X1>, X0>,
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y3>, Y2>, Y1>, Y0>,
            X0,
            X1,
            Y0,
            Y1,
            Y2,
            Y3
        );
        // 0b1XX < 0b1YYYYY
        $impl_mac!(
            UInt<UInt<UInt<UTerm, B1>, X1>, X0>,
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y4>, Y3>, Y2>, Y1>, Y0>,
            X0,
            X1,
            Y0,
            Y1,
            Y2,
            Y3,
            Y4
        );
        // 0b1XX < 0b1YYYYYY
        $impl_mac!(
            UInt<UInt<UInt<UTerm, B1>, X1>, X0>,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>,
            X0,
            X1,
            Y0,
            Y1,
            Y2,
            Y3,
            Y4,
            Y5
        );
        // 0b1XX < 0b1YYYYYYY
        $impl_mac!(
            UInt<UInt<UInt<UTerm, B1>, X1>, X0>,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y6>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>,
            X0,
            X1,
            Y0,
            Y1,
            Y2,
            Y3,
            Y4,
            Y5,
            Y6
        );

        //---------------------
        // 0b1000 < 0b1001
        $impl_mac!(U8, U9,);
        // 0b100X < 0b101Y
        $impl_mac!(
            UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, X0>,
            UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, Y0>,
            X0,
            Y0
        );
        // 0b100X < 0b11YY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, X0>,
            UInt<UInt<UInt<UInt<UTerm, B1>, B1>, Y1>, Y0>,
            X0,
            Y0,
            Y1
        );
        // 0b1010 < 0b1011
        $impl_mac!(U10, U11,);
        // 0b101X < 0b11YY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, X0>,
            UInt<UInt<UInt<UInt<UTerm, B1>, B1>, Y1>, Y0>,
            X0,
            Y0,
            Y1
        );
        // 0b1100 < 0b1101
        $impl_mac!(U12, U13,);
        // 0b110X < 0b111Y
        $impl_mac!(
            UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, X0>,
            UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, Y0>,
            X0,
            Y0
        );
        // 0b1100 < 0b1111
        $impl_mac!(U14, U15,);
        //---------------------
        // 0b1XXX < 0b1YYYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UTerm, B1>, X2>, X1>, X0>,
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y3>, Y2>, Y1>, Y0>,
            X0,
            X1,
            X2,
            Y0,
            Y1,
            Y2,
            Y3
        );
        // 0b1XXX < 0b1YYYYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UTerm, B1>, X2>, X1>, X0>,
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y4>, Y3>, Y2>, Y1>, Y0>,
            X0,
            X1,
            X2,
            Y0,
            Y1,
            Y2,
            Y3,
            Y4
        );
        // 0b1XXX < 0b1YYYYYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UTerm, B1>, X2>, X1>, X0>,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>,
            X0,
            X1,
            X2,
            Y0,
            Y1,
            Y2,
            Y3,
            Y4,
            Y5
        );
        // 0b1XXX < 0b1YYYYYYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UTerm, B1>, X2>, X1>, X0>,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y6>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>,
            X0,
            X1,
            X2,
            Y0,
            Y1,
            Y2,
            Y3,
            Y4,
            Y5,
            Y6
        );

        //---------------------
        // 0b1000X < 0b1001Y
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, EX0>,
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>, EY0>,
            EX0,
            EY0
        );
        // 0b100XX < 0b101YY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, X0>, EX0>,
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, Y0>, EY0>,
            X0,
            Y0,
            EX0,
            EY0
        );
        // 0b100XX < 0b11YYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, X0>, EX0>,
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, Y1>, Y0>, EY0>,
            X0,
            Y0,
            Y1,
            EX0,
            EY0
        );
        // 0b1010X < 0b1011Y
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, EX0>,
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B1>, EY0>,
            EX0,
            EY0
        );
        // 0b101XX < 0b11YYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, X0>, EX0>,
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, Y1>, Y0>, EY0>,
            X0,
            Y0,
            Y1,
            EX0,
            EY0
        );
        // 0b1100X < 0b1101Y
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, EX0>,
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B1>, EY0>,
            EX0,
            EY0
        );
        // 0b110XX < 0b111YY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, X0>, EX0>,
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, Y0>, EY0>,
            X0,
            Y0,
            EX0,
            EY0
        );
        // 0b1100X < 0b1111Y
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B0>, EX0>,
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>, EY0>,
            EX0,
            EY0
        );
        //---------------------
        // 0b1XXXX < 0b1YYYYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X3>, X2>, X1>, X0>,
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y4>, Y3>, Y2>, Y1>, Y0>,
            X0,
            X1,
            X2,
            X3,
            Y0,
            Y1,
            Y2,
            Y3,
            Y4
        );
        // 0b1XXXX < 0b1YYYYYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X3>, X2>, X1>, X0>,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>,
            X0,
            X1,
            X2,
            X3,
            Y0,
            Y1,
            Y2,
            Y3,
            Y4,
            Y5
        );
        // 0b1XXXX < 0b1YYYYYYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X3>, X2>, X1>, X0>,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y6>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>,
            X0,
            X1,
            X2,
            X3,
            Y0,
            Y1,
            Y2,
            Y3,
            Y4,
            Y5,
            Y6
        );

        //---------------------
        // 0b1000XX < 0b1001YY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, EX0>, EX1>,
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>, EY0>, EY1>,
            EX0,
            EY0,
            EX1,
            EY1
        );
        // 0b100XXX < 0b101YYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, X0>, EX0>, EX1>,
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, Y0>, EY0>, EY1>,
            X0,
            Y0,
            EX0,
            EY0,
            EX1,
            EY1
        );
        // 0b100XXX < 0b11YYYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, X0>, EX0>, EX1>,
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, Y1>, Y0>, EY0>, EY1>,
            X0,
            Y0,
            Y1,
            EX0,
            EY0,
            EX1,
            EY1
        );
        // 0b1010XX < 0b1011YY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, EX0>, EX1>,
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B1>, EY0>, EY1>,
            EX0,
            EY0,
            EX1,
            EY1
        );
        // 0b101XXX < 0b11YYYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, X0>, EX0>, EX1>,
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, Y1>, Y0>, EY0>, EY1>,
            X0,
            Y0,
            Y1,
            EX0,
            EY0,
            EX1,
            EY1
        );
        // 0b1100XX < 0b1101YY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, EX0>, EX1>,
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B1>, EY0>, EY1>,
            EX0,
            EY0,
            EX1,
            EY1
        );
        // 0b110XXX < 0b111YYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, X0>, EX0>, EX1>,
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, Y0>, EY0>, EY1>,
            X0,
            Y0,
            EX0,
            EY0,
            EX1,
            EY1
        );
        // 0b1100XX < 0b1111YY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B0>, EX0>, EX1>,
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>, EY0>, EY1>,
            EX0,
            EY0,
            EX1,
            EY1
        );
        //---------------------
        // 0b1XXXXX < 0b1YYYYYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X4>, X3>, X2>, X1>, X0>,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            Y0,
            Y1,
            Y2,
            Y3,
            Y4,
            Y5
        );
        // 0b1XXXXX < 0b1YYYYYYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X4>, X3>, X2>, X1>, X0>,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y6>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            Y0,
            Y1,
            Y2,
            Y3,
            Y4,
            Y5,
            Y6
        );

        //---------------------
        // 0b1000XXX < 0b1001YYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, EX0>, EX1>, EX2>,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>, EY0>, EY1>, EY2>,
            EX0,
            EY0,
            EX1,
            EY1,
            EX2,
            EY2
        );
        // 0b100XXXX < 0b101YYYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, X0>, EX0>, EX1>, EX2>,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, Y0>, EY0>, EY1>, EY2>,
            X0,
            Y0,
            EX0,
            EY0,
            EX1,
            EY1,
            EX2,
            EY2
        );
        // 0b100XXXX < 0b11YYYYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, X0>, EX0>, EX1>, EX2>,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, Y1>, Y0>, EY0>, EY1>, EY2>,
            X0,
            Y0,
            Y1,
            EX0,
            EY0,
            EX1,
            EY1,
            EX2,
            EY2
        );
        // 0b1010XXX < 0b1011YYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, EX0>, EX1>, EX2>,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B1>, EY0>, EY1>, EY2>,
            EX0,
            EY0,
            EX1,
            EY1,
            EX2,
            EY2
        );
        // 0b101XXXX < 0b11YYYYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, X0>, EX0>, EX1>, EX2>,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, Y1>, Y0>, EY0>, EY1>, EY2>,
            X0,
            Y0,
            Y1,
            EX0,
            EY0,
            EX1,
            EY1,
            EX2,
            EY2
        );
        // 0b1100XXX < 0b1101YYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, EX0>, EX1>, EX2>,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B1>, EY0>, EY1>, EY2>,
            EX0,
            EY0,
            EX1,
            EY1,
            EX2,
            EY2
        );
        // 0b110XXXX < 0b111YYYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, X0>, EX0>, EX1>, EX2>,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, Y0>, EY0>, EY1>, EY2>,
            X0,
            Y0,
            EX0,
            EY0,
            EX1,
            EY1,
            EX2,
            EY2
        );
        // 0b1100XXX < 0b1111YYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B0>, EX0>, EX1>, EX2>,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>, EY0>, EY1>, EY2>,
            EX0,
            EY0,
            EX1,
            EY1,
            EX2,
            EY2
        );
        //---------------------
        // 0b1XXXXXX < 0b1YYYYYYY
        $impl_mac!(
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X5>, X4>, X3>, X2>, X1>, X0>,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y6>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5,
            Y0,
            Y1,
            Y2,
            Y3,
            Y4,
            Y5,
            Y6
        );
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! impl_int_upty_ty1 {
    ($impl_mac:ident) => {
        $impl_mac!(
            u8,
            UInt<UInt<UInt<UInt<UTerm, B1>, X2>, X1>, X0>,
            X0,
            X1,
            X2
        );
        $impl_mac!(
            u8,
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3
        );
        $impl_mac!(
            u8,
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4
        );
        $impl_mac!(
            u8,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5
        );
        $impl_mac!(
            u8,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X6>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5,
            X6
        );

        $impl_mac!(
            u16,
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3
        );
        $impl_mac!(
            u16,
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4
        );
        $impl_mac!(
            u16,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5
        );
        $impl_mac!(
            u16,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X6>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5,
            X6
        );

        $impl_mac!(
            u32,
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4
        );
        $impl_mac!(
            u32,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5
        );
        $impl_mac!(
            u32,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X6>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5,
            X6
        );

        #[cfg(target_pointer_width = "32")]
        $impl_mac!(
            usize,
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4
        );
        #[cfg(target_pointer_width = "32")]
        $impl_mac!(
            usize,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5
        );
        #[cfg(target_pointer_width = "32")]
        $impl_mac!(
            usize,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X6>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5,
            X6
        );

        $impl_mac!(
            u64,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5
        );
        $impl_mac!(
            u64,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X6>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5,
            X6
        );

        #[cfg(target_pointer_width = "64")]
        $impl_mac!(
            usize,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5
        );
        #[cfg(target_pointer_width = "64")]
        $impl_mac!(
            usize,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X6>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5,
            X6
        );

        $impl_mac!(
            u128,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X6>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5,
            X6
        );
    };
}

/// Macro helper
#[macro_export]
#[doc(hidden)]
macro_rules! impl_int_ipty_ty1 {
    ($impl_mac:ident) => {
        $impl_mac!(
            i8,
            UInt<UInt<UInt<UInt<UTerm, B1>, X2>, X1>, X0>,
            X0,
            X1,
            X2
        );
        $impl_mac!(
            i8,
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3
        );
        $impl_mac!(
            i8,
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4
        );
        $impl_mac!(
            i8,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5
        );
        $impl_mac!(
            i8,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X6>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5,
            X6
        );

        $impl_mac!(
            i16,
            UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3
        );
        $impl_mac!(
            i16,
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4
        );
        $impl_mac!(
            i16,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5
        );
        $impl_mac!(
            i16,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X6>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5,
            X6
        );

        $impl_mac!(
            i32,
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4
        );
        $impl_mac!(
            i32,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5
        );
        $impl_mac!(
            i32,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X6>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5,
            X6
        );

        #[cfg(target_pointer_width = "32")]
        $impl_mac!(
            isize,
            UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4
        );
        #[cfg(target_pointer_width = "32")]
        $impl_mac!(
            isize,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5
        );
        #[cfg(target_pointer_width = "32")]
        $impl_mac!(
            isize,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X6>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5,
            X6
        );

        $impl_mac!(
            i64,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5
        );
        $impl_mac!(
            i64,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X6>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5,
            X6
        );

        #[cfg(target_pointer_width = "64")]
        $impl_mac!(
            isize,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5
        );
        #[cfg(target_pointer_width = "64")]
        $impl_mac!(
            isize,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X6>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5,
            X6
        );

        $impl_mac!(
            i128,
            UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X6>, X5>, X4>, X3>, X2>, X1>, X0>,
            X0,
            X1,
            X2,
            X3,
            X4,
            X5,
            X6
        );
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! impl_int_upty {
    ($impl_mac:ident) => {
        $impl_mac!(u8);
        $impl_mac!(u16);
        $impl_mac!(u32);
        $impl_mac!(usize);
        $impl_mac!(u64);
        $impl_mac!(u128);
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! impl_int_ipty {
    ($impl_mac:ident) => {
        $impl_mac!(i8);
        $impl_mac!(i16);
        $impl_mac!(i32);
        $impl_mac!(isize);
        $impl_mac!(i64);
        $impl_mac!(i128);
    };
}
