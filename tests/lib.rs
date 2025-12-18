mod attr;
mod html;
mod parse_events;

#[test]
fn list_bullet_type_to_u8() {
    assert_eq!(u8::from(jotdown::ListBulletType::Dash), b'-');
    assert_eq!(u8::from(jotdown::ListBulletType::Star), b'*');
    assert_eq!(u8::from(jotdown::ListBulletType::Plus), b'+');
}

#[test]
fn list_bullet_type_to_char() {
    assert_eq!(char::from(jotdown::ListBulletType::Dash), '-');
    assert_eq!(char::from(jotdown::ListBulletType::Star), '*');
    assert_eq!(char::from(jotdown::ListBulletType::Plus), '+');
}

#[test]
fn u8_to_list_bullet_type() {
    assert_eq!(b'-'.try_into(), Ok(jotdown::ListBulletType::Dash));
    assert_eq!(b'*'.try_into(), Ok(jotdown::ListBulletType::Star));
    assert_eq!(b'+'.try_into(), Ok(jotdown::ListBulletType::Plus));
    assert_eq!(jotdown::ListBulletType::try_from(b'='), Err(()));
}

#[test]
fn char_to_list_bullet_type() {
    assert_eq!('-'.try_into(), Ok(jotdown::ListBulletType::Dash));
    assert_eq!('*'.try_into(), Ok(jotdown::ListBulletType::Star));
    assert_eq!('+'.try_into(), Ok(jotdown::ListBulletType::Plus));
    assert_eq!(jotdown::ListBulletType::try_from('='), Err(()));
}
