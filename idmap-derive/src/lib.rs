#![recursion_limit = "128"]
extern crate proc_macro;

use quote::quote;

use proc_macro2::TokenStream;
use syn::{DeriveInput, Data, Lit, Expr, ExprLit, Fields};
use quote::ToTokens;

#[proc_macro_derive(IntegerId)]
pub fn integer_id(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = syn::parse(input).unwrap();
    impl_integer_id(&ast).into()
}

// The compiler doesn't seem to know when variables are used in the macro
#[allow(unused_variables)]
fn impl_integer_id(ast: &DeriveInput) -> TokenStream {
    let name = &ast.ident;
    match ast.data {
        Data::Struct(ref data) => {
            let fields = &data.fields;
            match fields.len() {
                1 => {
                    let field = fields.iter().next().unwrap();
                    /*
                     * NOTE: Delegating to the field's implementation allows efficient polymorphic overflow handling for all supported types.
                     * New types can be added to the library transparently, without changing the automatically derived implementation.
                     * Existing types can be improved by changing the implementation in one place, without touching the derived implementation.
                     * This should have zero overhead when inlining is enabled, since they're marked inline(always).
                     */
                    let field_type = &field.ty;
                    let (constructor, field_name) = match data.fields {
                        Fields::Named(_) => {
                            let field_name = field.ident.to_token_stream();
                            (quote!(#name { #field_name: value }), field_name)
                        },
                        Fields::Unnamed(_) => (quote! { #name( value ) }, quote!(0)),
                        Fields::Unit => unreachable!()
                    };
                    quote! {
                        impl ::idmap::IntegerId for #name {
                            #[inline(always)]
                            fn from_id(id: u64) -> Self {
                                let value = <#field_type as ::idmap::IntegerId>::from_id(id);
                                #constructor
                            }
                            #[inline(always)]
                            fn id(&self) -> u64 {
                                <#field_type as ::idmap::IntegerId>::id(&self.#field_name)
                            }
                            #[inline(always)]                    
                            fn id32(&self) -> u32 {
                                <#field_type as ::idmap::IntegerId>::id32(&self.#field_name)
                            }
                        }
                    }
                },
                0 => panic!("`IntegerId` is currently unimplemented for empty structs"),
                _ => panic!("`IntegerId` can only be applied to structs with a single field, but {} has {}", name, fields.len())
            }
        },
        Data::Enum(ref data) => {
            let mut idx = 0;
            let variants: Vec<_> = data.variants.iter().map(|variant| {
                let ident = &variant.ident;
                match variant.fields {
                    Fields::Unit => (),
                    _ => {
                        panic!("`IntegerId` can be applied only to unitary enums, {}::{} is either struct or tuple", name, ident)
                    },
                }
                match &variant.discriminant {
                    Some((_, Expr::Lit(ExprLit { lit: Lit::Int(value), .. }))) => {
                        idx = value.base10_parse::<u64>().expect("Unable to parse discriminant");
                    },
                    Some(_) => panic!("Can't handle discriminant for {}::{}", name, ident),
                    None => {}
                }
                let tt = quote!(#idx => #name::#ident);
                idx += 1;
                tt
            }).collect();
            quote! {
                impl ::idmap::IntegerId for #name {
                    #[inline]
                    fn from_id(id: u64) -> Self {
                        match id {
                            #(#variants,)*
                            _ => ::idmap::_invalid_id(id)
                        }
                    }
                    #[inline(always)]
                    fn id(&self) -> u64 {
                        *self as u64
                    }
                    #[inline(always)]
                    fn id32(&self) -> u32 {
                        *self as u32
                    }
                }
            }
        },
        Data::Union(_) => panic!("Unions are unsupported!")
    }
}
