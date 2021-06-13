use std::any::Any;

pub struct TypeHolder(Vec<Box<dyn Any>>);

impl TypeHolder {
    pub fn get_type_mut<T: Any + Default>(&mut self) -> &mut T {
        if let Some(i) = self
            .0
            .iter_mut()
            .position(|x| x.downcast_mut::<T>().is_some())
        {
            self.0[i].downcast_mut().unwrap()
        } else {
            let v: T = Default::default();
            self.0.push(Box::new(v));
            self.0.last_mut().unwrap().downcast_mut().unwrap()
        }
    }
    pub fn new() -> Self {
        TypeHolder(Vec::new())
    }
}
pub struct TypeHolderSend(Vec<AnySend>);

struct AnySend(Box<dyn Any + Send>);

impl TypeHolderSend {
    pub fn get_type_mut<T: Any + Send + Default>(&mut self) -> &mut T {
        if let Some(i) = self
            .0
            .iter_mut()
            .position(|x| x.0.downcast_mut::<T>().is_some())
        {
            self.0[i].0.downcast_mut().unwrap()
        } else {
            let v: T = Default::default();
            self.0.push(AnySend(Box::new(v)));
            self.0.last_mut().unwrap().0.downcast_mut().unwrap()
        }
    }
    pub const fn new() -> Self {
        TypeHolderSend(Vec::new())
    }
}
